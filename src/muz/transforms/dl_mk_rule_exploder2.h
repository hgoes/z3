#ifndef DL_MK_RULE_EXPLODER_
#define DL_MK_RULE_EXPLODER_

#include "dl_rule_transformer.h"
#include "dl_context.h"
#include "simplifier.h"
#include "tuple_set.h"
#include "bit_vector.h"

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
        bit_vector m_true;
        beta_reducer m_subst;
        simplifier m_simpl;
        unsigned m_threshold;
        void generate_mapping(const dataflow_engine<tuple_set>& engine, mapping_map& mappings, const rule_set& src, rule_set& trg);
        void translate_rule(const dataflow_engine<tuple_set>& engine, const mapping_map& mappings, rule* r, rule_set& trg);
    public:
        mk_rule_exploder2(context & ctx, unsigned threshold = 5, unsigned priority = 40000);
        rule_set * operator()(rule_set const & source);
    };

}

#endif
