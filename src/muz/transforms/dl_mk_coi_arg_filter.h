/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    dl_mk_coi_arg_filter.h

Abstract:

    Rule transformer that removes arguments of predicates if they are out of
    the cone of influence of the output predicates.

Author:
    Henning Guenther (t-hennig)

--*/

#ifndef DL_MK_COI_ARG_FILTER_H_
#define DL_MK_COI_ARG_FILTER_H_

#include "dataflow.h"
#include "arg_reachability.h"
#include "dl_rule_transformer.h"
#include "dl_context.h"
#include "map.h"

namespace datalog {
    
    class mk_coi_arg_filter : public rule_transformer::plugin {
        class coi_arg_model_converter;
        typedef obj_map<func_decl, func_decl*> repl_map;
        ast_manager& m;
        context& m_context;
        repl_map m_replacements;
        func_decl* get_replacement(repl_map& mp, rule_set const & source, func_decl *orig, const arg_reachability_info& info);
        app* get_replacement(repl_map& mp, rule_set const & source, app *orig, const arg_reachability_info& info);
        rule_set* transform(repl_map& mp, rule_set const & source, arg_reachability& engine);
    public:
        mk_coi_arg_filter(context & ctx, unsigned priority = 44000)
            : plugin(priority),
            m(ctx.get_manager()),
            m_context(ctx) {}
        rule_set * operator()(rule_set const & source);
        repl_map const& get_predicates() { return m_replacements; }
    };

}

#endif
