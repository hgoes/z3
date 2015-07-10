/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    arg_reachability.h

Abstract:

    Abstract domain for tracking argument reachability.

    In bottom-up mode it follows the following rules:

      1. If a predicate is instantiated with a constant in the head of a rule,
         then the corresponding argument is reachable. For example:

         A(x,3) :- B(x).
         B(x).

         Would result in argument 2 of predicate A being reachable.

      2. If the head of a rule contains a variable that appears in the
         interpreted tail of a rule, the corresponding argument is reachable.
         Consider:

         A(x) :- x<10.

         Here, argument 1 of predicate A would be marked reachable.

      3. If an argument of a predicate in the body of a rule is reachable and
         is instantiated with a variable, all arguments in the head where the
         variable appears will also become reachable. In the following:

         A(x,y) :- B(x) & C(y).

         Argument 2 of A becomes reachable when argument 1 of C is reachable.

    The top-down mode operates according to the following rules:

      1. All output predicates are reachable.

      2. All arguments that are instantiated with constants are reachable.

      3. If a variable in the head of a rule is in a reachable argument
         position, all occurances of that variable and variables dependent on
         it are marked reachable. If we have a rule like:

         A(x,y) :- B(x) & C(z) & y<z.

         Then argument 1 of b becomes reachable when argument 1 of A is
         reachable. Argument 1 of C becomes reachable when argument 2 of A is
         reachable, because its variable(z) depends on y.

Author:
    Henning Guenther (t-hennig)

--*/

#ifndef ARG_REACHABILITY_H_
#define ARG_REACHABILITY_H_

#include "dataflow.h"
#include "bit_vector.h"
#include "union_find.h"
#include "for_each_expr.h"

namespace datalog {
    class arg_reachability_info;
    typedef dataflow_engine<arg_reachability_info> arg_reachability;


    /* This class is used to track reachability across terms.
       For example, given the expression x=y & b=x+1 & z=a and the reachable
       set {b}, the taint tracer deduces that {b,x,y} are all reachable. */
    class taint_tracer : basic_union_find {
        unsigned m_root;
        unsigned m_reachable_root;
        expr_fast_mark1 m_visited;
    public:
        taint_tracer() {}
        
        void reset() {
            basic_union_find::reset();
            m_reachable_root = UINT_MAX;
        }

        // Add another conjunct to the considered formula.
        void process(expr* e) {
            m_root = UINT_MAX;
            for_each_expr_core<taint_tracer, expr_fast_mark1, false, true>(*this, m_visited, e);
            m_visited.reset();
        }

        // Mark a variable as reachable.
        void set_reachable(unsigned idx) {
            if (m_reachable_root == UINT_MAX) {
                m_reachable_root = find(idx);
            } else {
                m_reachable_root = merge(m_reachable_root, idx);
            }
        }

        // Check if a variable is reachable.
        bool is_reachable(unsigned v) const {
            return find(v) == m_reachable_root;
        }

        // Visitor interface. Do not call directly!
        void operator()(var* e) {
            SASSERT(e->get_idx() < UINT_MAX);
            unsigned idx = find(e->get_idx());
            if (m_root == UINT_MAX) {
                m_root = idx;
            } else if (m_reachable_root == m_root) {
                m_reachable_root = m_root = merge(m_root, idx);
            } else {
                m_root = merge(m_root, idx);
            }
        }

        // Visitor interface. Do not call directly!
        void operator()(app* e) const {}
        // Visitor interface. Do not call directly!
        void operator()(quantifier* e) const {}
    };

    struct arg_reachability_ctx {
        expr_free_vars m_fv;
        uint_set m_seen;
        taint_tracer m_tracer;
        ast_manager& m;
        const arg_reachability *m_prev;
        arg_reachability_ctx(ast_manager& m_, const arg_reachability *prev=0) : m(m_), m_prev(prev) {}
    };

    class arg_reachability_info {
        bit_vector m_reachable;
    public:
        typedef arg_reachability_ctx ctx_t;
        static const arg_reachability_info null_fact;
        arg_reachability_info() {}
        arg_reachability_info(func_decl *d) : m_reachable(d->get_arity()) {
            m_reachable.resize(d->get_arity());
        }

        static void init_down(ctx_t& m, const rule_set& rules, fact_setter<arg_reachability_info>& setter);
        bool init_up(ctx_t& m, const rule *r);
        bool propagate_up(ctx_t& m, const rule *r, const fact_reader<arg_reachability_info>& tail_facts);
        void propagate_down(ctx_t& manager, const rule *r, fact_writer<arg_reachability_info>& tail_facts) const;
        void join(ctx_t& manager, const arg_reachability_info& oth);
        void intersect(ctx_t& manager, const arg_reachability_info& oth);
        void dump(ctx_t& manager, std::ostream& outp) const;

        bool is_reachable(unsigned idx) const {
            return !m_reachable.empty() && m_reachable.get(idx);
        }

        bool any_reachable() const {
            for (unsigned i = 0; i < m_reachable.size(); ++i) {
                if (m_reachable.get(i))
                    return true;
            }
            return false;
        }

        bool all_reachable() const {
            for (unsigned i = 0; i < m_reachable.size(); ++i) {
                if (!m_reachable.get(i))
                    return false;
            }
            return true;
        }

        unsigned count_reachable() const {
            unsigned count = 0;
            for (unsigned i = 0; i < m_reachable.size(); ++i) {
                if (m_reachable.get(i))
                    ++count;
            }
            return count;
        }
    };
}

#endif
