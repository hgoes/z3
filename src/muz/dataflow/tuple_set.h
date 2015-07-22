#ifndef TUPLE_SET_H_
#define TUPLE_SET_H_

#include "dataflow.h"

#include "ast.h"
#include "vector.h"
#include "dl_rule.h"
#include "bit_vector.h"

namespace datalog {
    struct tuple_set_ctx;

    class tuple_set {
        func_decl* m_symbol;
        unsigned_vector m_indices;
        svector<expr*> m_tuples;
        bool has_tuples;
        unsigned m_num_cols;
        unsigned m_num_rows;
    public:
        typedef tuple_set_ctx ctx_t;
        bool is_finite(unsigned idx, unsigned& column) const {
            for (unsigned i = 0; i < m_num_cols; ++i) {
                if (m_indices[i] == idx) {
                    column = i;
                    return true;
                } else if (m_indices[i] > idx) {
                    return false;
                }
            }
            return false;
        }
        void delete_column(unsigned rcol) {
            SASSERT(m_num_cols == m_indices.size());
            SASSERT(m_tuples.size() == m_num_cols*m_num_rows);
            m_indices.erase(&m_indices[rcol]);
            unsigned offset = 0;
            unsigned pos = 0;
            for (unsigned row = 0; row < m_num_rows; ++row) {
                for (unsigned col = 0; col < m_num_cols; ++col) {
                    if (col == rcol) {
                        ++offset;
                    } else {
                        m_tuples[pos] = m_tuples[pos + offset];
                        ++pos;
                    }
                }
            }
            --m_num_cols;
            m_tuples.shrink(m_num_cols*m_num_rows);
        }
        void delete_columns(const unsigned_vector& rcols) {
            if (rcols.empty()) return;
            unsigned offset = 0;
            unsigned pos = 0;
            unsigned del_pos = 0;
            for (unsigned i = 0; i < m_indices.size(); ++i) {
                if (del_pos < rcols.size() && rcols[del_pos] == i) {
                    ++offset;
                } else {
                    m_indices[pos] = m_indices[pos + offset];
                    ++pos;
                }
            }
            m_indices.shrink(pos);
            offset = 0;
            pos = 0;
            for (unsigned row = 0; row < m_num_rows; ++row) {
                del_pos = 0;
                for (unsigned col = 0; col < m_num_cols; ++col) {
                    if (del_pos < rcols.size() && col == rcols[del_pos]) {
                        ++offset;
                        ++del_pos;
                    } else {
                        m_tuples[pos] = m_tuples[pos + offset];
                        ++pos;
                    }
                }
            }
            m_num_cols -= rcols.size();
            m_tuples.shrink(m_num_cols*m_num_rows);
        }
        void remove_duplicates() {
            SASSERT(m_num_cols == m_indices.size());
            SASSERT(m_tuples.size() == m_num_cols*m_num_rows);
            // Nothing to do?
            if (m_num_rows <= 1) 
                return;
            for (unsigned pos = 0; pos < m_num_rows-1; ++pos) {
                // Search for duplicates
                const unsigned pos_off = pos*m_num_cols;
                for (unsigned oth = pos + 1; oth < m_num_rows; ++oth) {
                    const unsigned oth_off = oth*m_num_cols;
                    bool equal = true;
                    for (unsigned i = 0; i < m_num_cols; ++i) {
                        if (m_tuples[pos_off + i] != m_tuples[oth_off + i]) {
                            equal = false;
                            break;
                        }
                    }
                    if (equal) {
                        //std::cout << "Removing duplicate row (" << m_num_rows << ")..." << std::endl;
                        --m_num_rows;
                        // Move all following rows
                        for (unsigned i = oth; i < m_num_rows; ++i) {
                            const unsigned i_off = i*m_num_cols;
                            for (unsigned j = 0; j < m_num_cols; ++j) {
                                m_tuples[i_off + j] = m_tuples[i_off + m_num_cols + j];
                            }
                        }
                        --oth;
                    }
                }
            }
            m_tuples.shrink(m_num_rows*m_num_cols);
        }
        bool deduce_var_facts(tuple_set_ctx& ctx, rule* r, const fact_reader<tuple_set>& facts);
        bool deduce_base_facts(tuple_set_ctx& ctx, const rule* r);
        void distribute_query_facts(ctx_t& ctx, const rule* r, fact_setter<tuple_set>& setter) const;
        static void distribute_query_fact(ctx_t& ctx, svector<expr*>& buffer, unsigned offs, const rule* r, fact_setter<tuple_set>& setter);
        bool insert_fact(ctx_t& ctx, svector<expr*>& fact_buffer, unsigned fact_offset);
        unsigned count_unique_values(ctx_t& ctx, unsigned col) const;
        void prune(ctx_t& ctx);
        bool is_full(ctx_t& ctx, unsigned col) const;
    public:
        unsigned num_cols() const {
            return m_num_cols;
        }
        unsigned num_rows() const {
            return m_num_rows;
        }
        static const tuple_set null_fact;
        tuple_set() : m_symbol(0), has_tuples(false), m_num_rows(0), m_num_cols(0) { }
        tuple_set(func_decl* sym) : m_symbol(sym), m_num_rows(0), m_num_cols(sym->get_arity()), m_indices(sym->get_arity()), has_tuples(false) {
            //m_indices.resize(m_num_cols);
            for (unsigned i = 0; i < m_num_cols; ++i) {
                m_indices[i] = i;
            }
        }
        const unsigned_vector& get_columns() const { return m_indices; }
        const svector<expr*>& get_tuples() const { return m_tuples; }
        bool init_up(ctx_t& ctx, const rule *r) {
            if (r->get_uninterpreted_tail_size() == 0)
                return deduce_base_facts(ctx, r);
            else
                return false;
        }
        bool propagate_up(ctx_t& ctx, rule* r, const fact_reader<tuple_set>& facts) {
            return deduce_var_facts(ctx, r, facts);
        }
        static void init_down(ctx_t& m, const rule_set& rules, fact_setter<tuple_set>& setter);
        void propagate_down(ctx_t& ctx, const rule* r, fact_writer<tuple_set>& tail_facts) const {
            distribute_query_facts(ctx, r, tail_facts);
        }
        void dump(ctx_t& ctx, std::ostream& outp) const;
        void intersect(ctx_t& ctx, const tuple_set& oth);
    };
    struct tuple_set_ctx {
        ast_manager& m;
        svector<expr*> m_buffer;
        unsigned_vector m_iter;
        svector<const tuple_set*> m_tail_facts;
        bit_vector m_seen;
        unsigned m_cutoff;
        tuple_set_ctx(ast_manager& _m, unsigned cutoff=5) : m(_m), m_cutoff(cutoff) {}
    };
}

#endif
