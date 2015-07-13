#ifndef VALUE_SET_H_
#define VALUE_SET_H_

#include "dataflow_arg.h"
#include "obj_hashtable.h"

namespace datalog {
    class value_set {
        obj_hashtable<expr> m_values;
        bool m_any_value;
    public:
        value_set(bool any = false);
        typedef ast_manager ctx_t;
        static value_set null_fact;
        static value_set full_fact;
        static void inference(ctx_t& ctx, var_facts<value_set>& facts, const rule* r);
        bool init_up(ctx_t& ctx, expr* arg);
        static void init_down(ctx_t& m, const rule_set& rules, fact_setter<value_set>& setter);
        bool join(ctx_t& ctx, const value_set& oth);
        bool join_constant(ctx_t& ctx, expr* value);
        bool intersect(ctx_t& ctx, const value_set& oth);
        void dump(ctx_t& ctx, std::ostream& outp) const;
        bool is_finite() const;
        const obj_hashtable<expr>& get_values() const;
        void deref(ctx_t& ctx);
    };

    typedef dataflow_engine<argument_fact<value_set> > value_set_engine;
}

#endif
