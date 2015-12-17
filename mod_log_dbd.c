/*  MOD_LOG_DBD     Apache 2.2 module

Copyright 2008  Tom Donovan

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

*/

#include "httpd.h"
#include "http_config.h"
#include "http_protocol.h"
#include "http_request.h"
#include "http_log.h"
#include "apr_lib.h"
#include "apr_dbd.h"
#include "apr_strings.h"
#include "mod_dbd.h"
#include "mod_log_config.h"

module AP_MODULE_DECLARE_DATA log_dbd_module;

#if AP_MODULE_MAGIC_AT_LEAST(20100606,0)
#define LOGLEVEL log.level
#else
#define LOGLEVEL loglevel
#endif
#ifdef APLOG_USE_MODULE
APLOG_USE_MODULE(log_dbd);
#endif 

/* log_dbd_module server configuration */
typedef struct {                
    apr_hash_t *files;
} log_dbd_svr_conf;

/* There is one of these in 'files' for every dbd-redirected log file */
typedef struct {
    const char *stmt_sql;       /* the SQL statement text */
    const char *stmt_label;     /* the (generated) label "log_dbd_N" */
    int useNull;
} log_dbd_file;

/* log_dbd_module request configuration */
typedef struct {
    ap_dbd_t *dbd;              /* acquired before handler if no fallback */
    } log_dbd_req_conf;

/* Used as a handle for log writer - has info to fallback to the orig writer */
typedef struct {
    char *name;    /* to look up entry in conf->files, NULL if not a dbd log */
    void *old_handle;           /* handle to pass to the old writer */
    ap_log_writer *old_writer;  /* the old (fallback) writer function */
    int format_checked;         /* the log format was already checked */
} log_dbd_handle;

/* optional functions imported from mod_log_config and mod_dbd */
static APR_OPTIONAL_FN_TYPE(ap_register_log_handler) *log_pfn_register_fn = NULL;
static APR_OPTIONAL_FN_TYPE(ap_log_set_writer_init) *log_set_writer_init_fn = NULL;
static APR_OPTIONAL_FN_TYPE(ap_log_set_writer) *log_set_writer_fn = NULL;
static APR_OPTIONAL_FN_TYPE(ap_dbd_prepare) *dbd_prepare_fn = NULL;
static APR_OPTIONAL_FN_TYPE(ap_dbd_acquire) *dbd_acquire_fn = NULL;

/* Original writer and writer_init functions (restore on dso unload!) */
static ap_log_writer *orig_writer = NULL;
static ap_log_writer_init *orig_writer_init = NULL;

/* check if a string could be a label name */
#define MAX_LABEL_SIZE 32
static APR_INLINE int isSimpleName(const char *s) 
{   
    if (strlen(s) > MAX_LABEL_SIZE)
        return 0;
    for (; *s ; s++)
        if (!apr_isalnum(*s) && (*s != '_') && (*s != '-'))
            return 0;
    return 1;
}

/* Escape single quotes in a string by doubling them */
static char *esq(apr_pool_t *p, const char *s)
{   
    char *newstr, *src, *dst, *sq;
    int qcount;

    /* return the original if there are no single-quotes */
    if (!(sq = strchr(s, '\''))) 
        return (char *) s;
    /* count the single-quotes and allocate a new buffer */
    for (qcount = 1; sq = strchr(sq + 1, '\''); )
        qcount++;
    newstr = apr_palloc(p, strlen(s) + qcount + 1);

    /* move chars, doubling all single-quotes */
    src = (char *) s;
    for (dst = newstr ; *src ; src++) {
        if ((*dst++ = *src) == '\'')  
            *dst++ = '\'';
    }
    *dst = 0;
    return newstr;
}
/* All the letters which can be in an APR 1.3 parameter marker */
#define PARAM_MARKER_LETTERS "shdulfpDtiazbcn"
/* Used when the database is inaccessible. Writes SQL statements to log file */
static apr_status_t write_fallback_log(request_rec *r, 
                                       log_dbd_handle *handle, 
                                       log_dbd_file *file, 
                                       const char **strs, 
                                       int nelts)
{   
    const char **nstrs;
    int *nstrl;
    char *start, *end, *sql;
    int inliteral, nsize, i=0, j=0;
    apr_size_t len;

    /* Build a new array of strings merging the SQL statement
     * and the elements of strs enclosed in single-quotes,
     * escaping any single-quotes contained in the element.
     *
     * Parameter markers can either be the single character ?
     * or else % followed by any combination of the letters "shdulfpDtiazbcn"
     *
     * Note that parameter markers cannot occur inside a 'string literal' in the SQL.
     *
     * Each strs element will require nstrs to contain:
     * 1) preceeding SQL text    2) a leading single-quote 
     * 3) the (escaped) element  4) a trailing single-quote
     * the trailing SQL text and semicolon account for two more.
     */
    nsize = nelts * 4 + 2;
    nstrs = (const char **) apr_pcalloc(r->pool, nsize * sizeof(char *));
    nstrl = (int *) apr_pcalloc(r->pool, nsize * sizeof(int));
    if (isSimpleName(file->stmt_sql) && nelts) {
        /* For a single WORD (probably created with DBDPrepareSQL) which has arguments
         * generate pseudo-SQL like "WORD(?,?,?,...)" 
         */
        char *sptr;
        int n;
        sql = apr_pcalloc(r->pool, strlen(file->stmt_sql) + (nelts * 2) + 2);
        sptr = sql;
        sptr = apr_cpystrn(sptr, file->stmt_sql, MAX_LABEL_SIZE);
        *sptr++ = '(';
        *sptr++ = '?';
        for (n=1 ; n < nelts ; n++) {
            *sptr++ = ',';
            *sptr++ = '?';
        }
        *sptr++ = ')';
        *sptr++ = 0;
    }
    else
        sql = (char *) file->stmt_sql;
    start = end = sql;
    inliteral = 0;
    while (nelts && (end = strpbrk(end, "?%'"))) { 
        /* It can't be a param inside a string literal 
         * - even if looks like one 
        */
        if (!inliteral) {
            if (*end == '\'') {
                inliteral = 1;
                end++;
                continue;
            }
            /* Found a parameter marker - use a space to avoid 
             * adjacent ' chars or adjacent NULLNULL substitutions
             */
            nstrs[i++] = (end > start || end == file->stmt_sql) ? 
                apr_pstrndup(r->pool, start, end-start) : " ";
            if (strs[j]) {
                nstrs[i++] = "'";
                nstrs[i++] = esq(r->pool, strs[j++]);
                nstrs[i++] = "'";
            }
            else {
                nstrs[i++] = "NULL";
                j++;
            }
            --nelts;
            start = end + 1
                + ( (*end == '%') ? strspn(end + 1, PARAM_MARKER_LETTERS) : 0);
            end = start;
        }
        /* Look for the end of the string literal */
        else {
            if (*end++ == '\'') {
                if (*end == '\'') 
                    end++;
                else 
                    inliteral = 0;
            }
        }
    }
    /* any trailing SQL? */
    if (start && *start) 
        nstrs[i++] = start;
    nstrs[i++] = ";" APR_EOL_STR;
    /* Calculate totals and call the original writer */
    for (len = j = 0; j < i ; j++) {
        nstrl[j] = (int) strlen(nstrs[j]);
        len += nstrl[j];
    }


    if (!handle->old_writer) {
        /* logging SQL to error log, len includes ";CRLF" */
        char *str = apr_palloc(r->pool, len);
        char *s;
        for (j = 0, s = str; j < (i - 1) ; ++j) {
            memcpy(s, nstrs[j], nstrl[j]);
            s += nstrl[j];
        }
        /* terminate with semicolon, but no CRLF */
        *s++ = ';';
        *s++ = 0;
        /* replace all ctrl-chars (i.e. tabs) with spaces */
        for (s = str ; *s ; s++)
            if (*s < ' ')
                *s = ' ';
        ap_log_rerror(APLOG_MARK, 
            (r->server->LOGLEVEL == APLOG_DEBUG) ? APLOG_DEBUG : APLOG_ERR, 
            0, r, "mod_log_dbd: %s", str);
        return APR_EGENERAL;
    }
    else
        /* a fallback log file was specified */
        return handle->old_writer(r, handle->old_handle, nstrs, nstrl, i, len);
}

/* DBD log writer */
static apr_status_t write_log(request_rec *r,
                              void *hndl,
                              const char **strs,
                              int *strl,
                              int nelts,
                              apr_size_t len)
{   
    log_dbd_handle *handle = (log_dbd_handle *) hndl;
    ap_dbd_t *dbd;
    apr_dbd_prepared_t *stmt;
    apr_dbd_prepared_t *prestmt;
    int rows = 0;
    int rv = 0;
    log_dbd_svr_conf *conf; 
    log_dbd_req_conf *rconf;
    log_dbd_file *file;     
    const char **newstrs = strs;
    int newnelts = nelts;

    /* Just call the old writer if we are not using dbd for this log */
    if (!handle->name) 
        return (handle->old_writer)(r, handle->old_handle, 
                                    strs, strl, nelts, len);

    /* Get our config and the SQL stmt for this Virtual Host */
    conf = (log_dbd_svr_conf *) ap_get_module_config(r->server->module_config, 
                                                &log_dbd_module);
    rconf = (log_dbd_req_conf *) ap_get_module_config(r->request_config, 
                                                &log_dbd_module);
    file = apr_hash_get(conf->files, handle->name, APR_HASH_KEY_STRING);

    if (nelts) {
        int orig, unsep;

        /* mod_log_config currently adds an EOL string*/
        if (!strcmp(strs[nelts-1], APR_EOL_STR)) 
            --nelts;

        /* Build new strs/nelts using only the odd-numbered log fields */
        newstrs = 
            (const char **) apr_pcalloc(r->pool, 
                                        ((nelts + 1) / 2) * sizeof(char*));
        for (orig = unsep = 0; orig < nelts ; unsep++) {
            /* Use only the odd-numbered fields. */
            newstrs[unsep] = strs[orig++];
            /* substitute NULL for "-" */
            if (file->useNull && (newstrs[unsep][0] == '-') && (!newstrs[unsep][1]) )
                newstrs[unsep] = NULL;

            /* Confirm that all the even-numbered fields are valid separators 
             * (one comma and optional spaces or tabs), and discard them.
             * Only check log format separators the first time through, 
             * since log formats cannot change at runtime.
             */
            if (!handle->format_checked && orig < nelts) {
                char *sep = strchr(strs[orig], ',');
                if (!sep 
                    || strchr(sep+1, ',') 
                    || strspn(strs[orig], " \t,") != strlen(strs[orig]) 
                    ) {
                    ap_log_rerror(APLOG_MARK, APLOG_CRIT, 0, r,
                        "mod_log_dbd: Invalid log format used with mod_log_dbd - "
                        "must contain only comma-separated log format codes");
                    ap_log_rerror(APLOG_MARK, APLOG_ERR, 0, r,
                        "mod_log_dbd: Request was not logged");
                    return APR_EGENERAL;
                }
            }
            orig++;
        }
        newnelts = unsep;
        handle->format_checked = 1; 
    }
    /* try to get a connection */
    if ((dbd = dbd_acquire_fn(r)) == NULL) {
        ap_log_rerror(APLOG_MARK, APLOG_ERR, 0, r,
            "mod_log_dbd: Error acquiring connection to database, logging SQL to %s",
            handle->name);
        return write_fallback_log(r, handle, file, newstrs, newnelts);
    }
    /* file->stmt_sql might just be a label created with DBDPrepareSQL, not real SQL */
    if (isSimpleName(file->stmt_sql) 
        && (prestmt = apr_hash_get(dbd->prepared, file->stmt_sql, APR_HASH_KEY_STRING))) {
            stmt = prestmt;
    }
    /* otherwise, get our real prepared statement */
    else if ((stmt = apr_hash_get(dbd->prepared, file->stmt_label, 
                             APR_HASH_KEY_STRING)) == NULL) {
        ap_log_rerror(APLOG_MARK, APLOG_ERR, 0, r,
            "mod_log_dbd: Unable to retrieve prepared statement %s, logging SQL to %s", 
            file->stmt_label, handle->name);
        return write_fallback_log(r, handle, file, newstrs, newnelts);
    }

    /* perform the query */
    if (rv = apr_dbd_pquery(dbd->driver, r->pool, dbd->handle, &rows, stmt, 
                            newnelts, newstrs)) {
        ap_log_rerror(APLOG_MARK, APLOG_ERR, 0, r,
            "mod_log_dbd: Unable to execute SQL statement: %s logging SQL to %s", 
            apr_dbd_error(dbd->driver, dbd->handle, rv), handle->name);
        return write_fallback_log(r, handle, file, newstrs, newnelts);
    }
    else {
        /* DEBUG loglevel - generating SQL is a lot of work, so we check first */
        if (r->server->LOGLEVEL == APLOG_DEBUG) {
            /* use a NULL handle to write SQL to error log */
            log_dbd_handle *dbghndl = apr_pmemdup(r->pool, handle, sizeof(log_dbd_handle));
            dbghndl->old_writer = NULL;
            ap_log_rerror(APLOG_MARK, APLOG_DEBUG, 0, r,
                "mod_log_dbd: Successfully executed %s (stmt: %s): rows updated = %d, ",
                         handle->name,
                         file->stmt_label,
                         rows);
            write_fallback_log(r, dbghndl, file, newstrs, newnelts);
        }
    }
    return 0; 
}

/* DBD log writer init */
static void *log_writer_init(apr_pool_t *p, server_rec *s,
                                        const char* name)
{   
    log_dbd_svr_conf *conf = 
        (log_dbd_svr_conf *) ap_get_module_config(s->module_config, &log_dbd_module);
    log_dbd_file *file = (log_dbd_file *) apr_hash_get(conf->files, name, APR_HASH_KEY_STRING);
    log_dbd_handle *handle = apr_pcalloc(p, sizeof(log_dbd_handle));

    /* Save the name.  We look up the SQL stmt at log-writing time because 
     * we may use a different SQL stmt for the same name in different Virtual Hosts
     */
    if (apr_hash_get(conf->files, name, APR_HASH_KEY_STRING))
        handle->name = apr_pstrdup(p, name);
    /* always init the old log writer for fallback */
    handle->old_handle = orig_writer_init(p, s, name);
    handle->old_writer = orig_writer;
    return handle;
}


/* process DBDLog directive */
static const char *setAccessLogQuery(cmd_parms *cmd, void *mconfig, 
                                     const char *name, const char *sql, const char *usenull)
{   
    static long label_num = 0;
    log_dbd_file *file = apr_pcalloc(cmd->pool, sizeof(log_dbd_file));
    log_dbd_svr_conf *conf = 
        (log_dbd_svr_conf *) ap_get_module_config(cmd->server->module_config,
                                              &log_dbd_module);
    if (!dbd_prepare_fn || !dbd_acquire_fn)
        return "mod_dbd must be enabled to use mod_log_dbd";

    if (!log_set_writer_init_fn || !log_set_writer_fn) 
        return "mod_log_config must be enabled to use mod_log_dbd";

    file->stmt_sql = sql;
    file->stmt_label = apr_pstrcat(cmd->pool, "log_dbd_", 
                                   apr_ltoa(cmd->pool, ++label_num), NULL);
    dbd_prepare_fn(cmd->server, sql, file->stmt_label);

    ap_log_error(APLOG_MARK, APLOG_DEBUG, 0, cmd->server,
        "mod_log_dbd: Prepared query (stmt: %s) from: %s",
        file->stmt_label, sql);

    apr_hash_set(conf->files, name, APR_HASH_KEY_STRING, file);

    if (usenull) {
        if(!apr_strnatcasecmp(usenull, "UseNULLs"))
            file->useNull = 1;
        else
             return apr_pstrcat(cmd->pool, "mod_log_dbd: unrecognized option: ",
                                    usenull, NULL);
    }
    return NULL;
}

static void *merge_config_server(apr_pool_t *p, void *parentconf, 
                                 void *newconf)
{   log_dbd_svr_conf *base = (log_dbd_svr_conf *) parentconf;
    log_dbd_svr_conf *add = (log_dbd_svr_conf *) newconf;

    add->files = apr_hash_overlay(p, add->files, base->files);
    return add;
}


/* need to restore the init_writer & writer functions on a dso unload */
static void revert_writers(void)
{
        module *mod_log_config = ap_find_linked_module("mod_log_config.c");

        if (mod_log_config 
                && log_set_writer_fn && log_set_writer_init_fn
                && orig_writer && orig_writer_init) {
            log_set_writer_fn(orig_writer);
            log_set_writer_init_fn(orig_writer_init);
        }
}


static void *config_server(apr_pool_t *p, server_rec *s)
{
    log_dbd_svr_conf *conf = apr_pcalloc(p, sizeof(log_dbd_svr_conf));

    if (!log_pfn_register_fn) {
        log_pfn_register_fn =
                    APR_RETRIEVE_OPTIONAL_FN(ap_register_log_handler);
        log_set_writer_init_fn =
                    APR_RETRIEVE_OPTIONAL_FN(ap_log_set_writer_init);
        log_set_writer_fn =
                    APR_RETRIEVE_OPTIONAL_FN(ap_log_set_writer);
        dbd_prepare_fn =
                    APR_RETRIEVE_OPTIONAL_FN(ap_dbd_prepare);
        dbd_acquire_fn =
                    APR_RETRIEVE_OPTIONAL_FN(ap_dbd_acquire);
    }
    conf->files = apr_hash_make(p);
    return conf;
}

static int pre_config(apr_pool_t *p, apr_pool_t *plog, apr_pool_t *ptemp)
{
    if (!log_set_writer_init_fn || !log_set_writer_fn) {
        ap_log_perror(APLOG_MARK, APLOG_ERR, 0, plog, 
                        "mod_log_config is required by mod_log_dbd");
        return 500;    
    }

    if (!orig_writer_init) {
        module *mod_log_config = ap_find_linked_module("mod_log_config.c");
        orig_writer_init = log_set_writer_init_fn(log_writer_init);
        orig_writer = log_set_writer_fn(write_log);
        /* if we are dynamic, put the original 
         * function ptrs back so mod_log_config won't have bogus pointers - or 
          * worse, give us our own functions back as old_writer if we get re-loaded! 
         */
        if (mod_log_config && log_dbd_module.dynamic_load_handle)
            atexit(revert_writers);
    }
	return OK;
}
static const command_rec cmds[] =
{
    AP_INIT_TAKE23("DBDLog", setAccessLogQuery, 
                   NULL, RSRC_CONF, "DBDLog  NAME  QUERY  [UseNULLs]"),
    {NULL}
};
static void register_hooks(apr_pool_t *p)
{
    static const char * const aszPred[]={ "mod_log_config.c", NULL };
    ap_hook_pre_config(pre_config,aszPred,NULL,APR_HOOK_LAST);
}

module AP_MODULE_DECLARE_DATA log_dbd_module =
{
    STANDARD20_MODULE_STUFF,
    NULL,                       /* create per-dir config */
    NULL,                       /* merge per-dir config */
    config_server,              /* server config */
    merge_config_server,        /* merge server config */
    cmds,                       /* command apr_table_t */
    register_hooks              /* register hooks */
};
