#ifndef _DL_MK_RULE_EXPLODER_H_
#define _DL_MK_RULE_EXPLODER_H_

#include "dl_rule_transformer.h"
#include "dl_context.h"
#include "value_set.h"

namespace datalog {

    class mk_rule_exploder : public rule_transformer::plugin {
        struct iter_state {
            obj_hashtable<expr>::iterator m_begin;
            obj_hashtable<expr>::iterator m_end;
            obj_hashtable<expr>::iterator m_cur;
            iter_state(const obj_hashtable<expr>& set) : m_begin(set.begin()), m_end(set.end()), m_cur(set.begin()) {}
        };
        struct tail_pos {
            unsigned m_tail_num;
            unsigned m_arg_num;
            tail_pos(unsigned t, unsigned arg) : m_tail_num(t), m_arg_num(arg) {}
        };
        enum fix_type {
            FIXED_CONST,
            FIXED_ITER
        };
        struct fix_descr {
            fix_type m_type;
            union {
                unsigned m_iterator;
                expr* m_const;
            };
            fix_descr(unsigned it) : m_type(FIXED_ITER), m_iterator(it) {}
            fix_descr(expr* c) : m_type(FIXED_CONST), m_const(c) {}
            fix_descr() : m_type(FIXED_CONST), m_const(0) {}
        };
        struct tail_state {
            func_decl* m_decl;
            const argument_fact<value_set>* m_fact;
            vector<expr*> m_instantiation;
            tail_state() : m_decl(0), m_fact(&argument_fact<value_set>::null_fact) {}
        };
        struct todo_entry {
            func_decl* m_orig;
            func_decl* m_new;
            const argument_fact<value_set>& m_fact;
            vector<expr*> m_inst;
            todo_entry(func_decl* o, func_decl* n, vector<expr*> i, const argument_fact<value_set>& f) : m_orig(o), m_new(n), m_inst(i), m_fact(f) {}
        };
        typedef map<vector<expr*>, func_decl*, vector_hash<ptr_hash<expr> >, vector_eq_proc<vector<expr*> > > inst_mapping;
        typedef map<func_decl*, inst_mapping*, ptr_hash<func_decl>, default_eq<func_decl*> > mapping;
        context& m_context;
        value_set_engine* m_engine;
        vector<todo_entry> m_todo;
        mapping m_mapping;

        const rule_set* m_source;
        rule_set* m_target;

        const rule* m_rule;
        
        vector<tail_state> m_tail_state;
        obj_map<expr, fix_descr> m_fixed;
        vector<iter_state> m_iters;

        // Caches
        vector<expr*> m_arg_cache;
        vector<app*> m_app_cache;
        vector<expr*> m_inst_cache;
        vector<bool> m_neg_cache;

        void set_rule(const rule* r);
        bool get_fixed_head(const todo_entry& cur);
        bool fix_var(expr* var, expr* c);
        app* fix_app(app* orig);
        expr* fix_expr(expr* orig);
        bool check_tail();
        void init_tail_state();
        bool inc_iteration();
        void get_iteration(vector<expr*>& inst) const;
        func_decl* get_mapping(func_decl* orig, const argument_fact<value_set>& fact, vector<expr*>& inst);
        rule* make_rule(const todo_entry& cur);
        bool step();
    public:
        mk_rule_exploder(context & ctx, unsigned priority = 40000);
        rule_set * operator()(rule_set const & source);
    };
}

#endif
