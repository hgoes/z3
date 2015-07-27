#ifndef DL_MK_RULE_EXPLODER_
#define DL_MK_RULE_EXPLODER_

#include "dl_rule_transformer.h"
#include "dl_context.h"
#include "simplifier.h"
#include "tuple_set.h"
#include "bit_vector.h"
#include "for_each_expr.h"

namespace datalog {

    class mk_rule_exploder2 : public rule_transformer::plugin {
        typedef map<func_decl*, vector<func_decl*>, obj_ptr_hash<func_decl>, ptr_eq<func_decl> > mapping_map;
        context& m_ctx;
        unsigned_vector m_iters;
        vector<const tuple_set*> m_tail_facts;
        vector<vector<func_decl*>*> m_tail_syms;
        app_ref_vector m_new_tail;
        svector<bool> m_new_tail_neg;
        expr_ref_vector m_new_args;
        vector<expr*> m_var_bindings;
        vector<sort*> m_var_sorts;
        beta_reducer m_subst;
        simplifier m_simpl;
        unsigned m_threshold;
        uint_set m_bound_vars;
        uint_set m_exluded_tails;
        struct contains_bound_var {
            bool m_contains_bound_var;
            vector<var*> m_unbound_vars;
            uint_set& m_bound_vars;
            expr_fast_mark1 m_visited;
            contains_bound_var(uint_set& bound_vars) : m_contains_bound_var(false), m_bound_vars(bound_vars) {}
            void process(expr *e) {
                for_each_expr_core<contains_bound_var, expr_fast_mark1, false, true>(*this, m_visited, e);
                m_visited.reset();
            }
            void reset() {
                m_contains_bound_var = false;
                m_unbound_vars.reset();
            }
            // Visitor interface. Do not call directly!
            void operator()(var* e) {
                if (m_contains_bound_var)
                    return;
                const unsigned vidx = e->get_idx();
                if (m_bound_vars.contains(vidx)) {
                    m_contains_bound_var = true;
                } else {
                    for (unsigned i = 0; i < m_unbound_vars.size(); ++i) {
                        if (m_unbound_vars[i] == e)
                            return;
                    }
                    m_unbound_vars.push_back(e);
                }
            }

            // Visitor interface. Do not call directly!
            void operator()(app* e) const {}
            // Visitor interface. Do not call directly!
            void operator()(quantifier* e) const {}
        };
        contains_bound_var m_contains_bound_var;
        struct negation_repl_key {
            func_decl* m_symbol;
            vector<expr*> m_inst;
            unsigned m_hash_cache;
            negation_repl_key(ast_manager& m) : m_hash_cache(0) {}
            unsigned hash() {
                if (m_hash_cache != 0)
                    return m_hash_cache;
                unsigned r = m_symbol->hash();
                for (unsigned i = 0; i < m_inst.size(); ++i) {
                    if (m_inst.get(i)) {
                        r = combine_hash(r, m_inst.get(i)->hash());
                    } else {
                        r = combine_hash(r, hash_u(i));
                    }
                }
                m_hash_cache = r;
                return r;
            }
            bool operator==(const negation_repl_key & o) const {
                return o.m_symbol == m_symbol && vectors_equal(o.m_inst, m_inst);
            }
        };
        negation_repl_key* m_cur_key;
        obj_map<negation_repl_key, func_decl*> m_negation_repl;
        void generate_mapping(const dataflow_engine<tuple_set>& engine, mapping_map& mappings, const rule_set& src, rule_set& trg);
        void translate_rule(const dataflow_engine<tuple_set>& engine, const mapping_map& mappings, rule* r, rule_set& trg);
        app* get_negation_replacement(func_decl* sym, expr_ref_vector& inst, const dataflow_engine<tuple_set>& engine, const mapping_map& mappings, rule_set& trg);
        rule* create_common_tail(const rule* r, app_ref& common_tail);
    public:
        mk_rule_exploder2(context & ctx, unsigned threshold = 1, unsigned priority = 40000);
        rule_set * operator()(rule_set const & source);
    };

}

#endif
