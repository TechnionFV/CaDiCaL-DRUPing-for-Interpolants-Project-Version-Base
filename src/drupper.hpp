#ifndef _drupper_hpp_INCLUDED
#define _drupper_hpp_INCLUDED

/*-----------------------------------------------------------------------------------

  The code implements the algorithm introduced in "DRUPing For Interpolant",
  a paper by Arie Gurfinkel and Yakir Vizel. Drupper allows DRUP-based proof
  trimming, validation, interpolants and core extraction enabled by
  'opts.drup'.

  Limitations:
    - Allowing other proof observers/checkers in parallel:
      During validation/trimming procedure, drupper can delete or revive
      clauses that other Internal::Proof observers aren't aware of. As a
      result, enabling such observers and checkers in parallel might trigger
      errors.

    - Chronological backtracking enabled by 'opts.chrono':
      The combination of chronological backtracking with the algorithm is
      challenging since invariants classically considered crucial to CDCL
      cease to hold. In its current implementation, the algorithm relies on
the level order invariant which ensures the literals are ordered on the
      assignment trail in ascending order with respect to their decision
level. This invariant is violated. In the interest of compatibility with
      chronological backtracking, adjustments to the implementation will be
      considered in the future.

    - Incompatible [in/pre]processing techniques:
      1) probing / advanced probing / lookahead: not resolution based.
      2) conditioning / blocking: is this some sort of of BCE?
      3) compacting: variables are revived in the process.
      4) vivication: vivified (reason) clause must maintain first literal in
      place.

    - Avoid propagating binary clauses as soon as they are marked as
      garbage.

-----------------------------------------------------------------------------------*/

namespace CaDiCaL {

class LiteralSort {
  Internal *internal;

public:
  LiteralSort (Internal *i);
  bool operator() (int x, int y) const;
};

struct ChainDerivation {
  vector<int> pivots;
  vector<Clause *> clauses;
  void clear ();
  void append (Clause *);
  void append (int, Clause *);
  bool empty () const;
};

struct ResolutionProofIterator {
  virtual ~ResolutionProofIterator () {}
  virtual void resolution (int, int, Clause *) = 0;
  virtual void chain_resolution (ChainDerivation &, int) = 0;
  virtual void chain_resolution (ChainDerivation &, Clause *parent = 0) = 0;
};

enum DCVariant { CLAUSE = 0, LITERALS = 1 };

// A deallocated Clause object will have a DrupperClause counterpart object
// maintaining its literals and color range in a single std::vector<int>.
// For a clause of size N, we maintain a vector of size N+1 s.t.:
// - literals are kept in entries 0, ..., N-1.
// - range is encoded to an integer and is in entry [N].
//
// This iterator excludes the last entry, which is color range code integer.
class DrupperClauseIterator {
private:
  const vector<int> &m_clause;
  size_t m_index;

public:
  explicit DrupperClauseIterator (const vector<int> &, size_t);
  int operator* () const;
  DrupperClauseIterator &operator++ ();
  DrupperClauseIterator &operator+ (int);
  bool operator!= (const DrupperClauseIterator &other) const;
};

class DrupperClause {
  bool variant : 1;

public:
  bool deleted : 1;
  unsigned revive_at : 30;

protected:
  union {
    Clause *counterpart;
    vector<int> *literals;
  };
  const vector<int> &lits () const;

public:
  DrupperClause (vector<int> c, int code, bool deletion = false);
  DrupperClause (Clause *c, bool deletion = false);
  ~DrupperClause ();
  DCVariant variant_type () const;
  void destroy_variant ();
  void set_variant (Clause *);
  Clause *flip_variant ();
  Clause *clause ();
  int color_range_code () const;
  int size () const;
  DrupperClauseIterator lits_begin () const;
  DrupperClauseIterator lits_end () const;
};

class ColorRange {
  unsigned m_min : 16, m_max : 16;

public:
  ColorRange ();
  ColorRange (const unsigned);
  bool undef () const;
  void reset ();
  bool singleton () const;
  void join (const unsigned np);
  void join (const ColorRange &o);
  unsigned min () const;
  unsigned max () const;
  bool operator== (const ColorRange &r);
  bool operator!= (const ColorRange &r);
  void operator= (int);
  int code () const;
};

struct lock_scope {
  bool &key;
  lock_scope (bool &key_) : key (key_) {
    assert (!key_);
    key = true;
  }
  ~lock_scope () { key = false; }
};

template <class T> struct save_scope {
  T &key;
  T initial;
  save_scope (T &key_) : key (key_), initial (key_) {}
  save_scope (T &key_, T val_within_scope) : key (key_), initial (key_) {
    key = val_within_scope;
  }
  ~save_scope () { key = initial; }
};

class Drupper {

  Internal *internal;

  // stack of clausal proof
  //
  vector<DrupperClause *> proof;

  Clause *new_redundant_clause (const vector<int> &);
  Clause *new_redundant_clause (const DrupperClause *);
  // to keep up with internal->stats
  void mark_garbage (Clause *);
  void mark_active (Clause *);
  Clause *new_unit_clause (int, bool);
  void delete_garbage_unit_clauses ();
  vector<Clause *> unit_clauses;

  Clause *failed_constraint, *final_conflict;
  bool isolated, in_action, overconstrained;
  vector<Clause *> failing_assumptions;

  bool satisfied (Clause *) const;
  bool trivially_satisfied (const vector<int> &);
  bool clauses_are_identical (Clause *, const vector<int> &) const;
  void append_lemma (DrupperClause *);
  void revive_clause (int);
  void stagnate_clause (Clause *);
  void reactivate_fixed (int);
  void reactivate (Clause *);

  // Trimming
  //
  void shrink_internal_trail (const unsigned);
  void clean_conflict ();

  void undo_trail_literal (int);
  void undo_trail_core (Clause *, unsigned &);
  bool is_on_trail (Clause *) const;

  void mark_core (Clause *);
  void mark_conflict_lit (int);
  void mark_conflict ();

  void assume_negation (const Clause *);
  bool propagate_conflict (bool core = false);
  bool reverse_unit_propagation (Clause *, bool core = false);
  bool got_value_by_propagation (int) const;
  void conflict_analysis_core ();

  void mark_core_trail_antecedents ();
  void unmark_core ();
  void restore_trail (bool initial_data_base = false);
  void restore_proof_garbage_marks ();
  void reconstruct (unsigned);

  void check_environment () const;
  void dump_clauses (bool active = false) const;
  void dump_clause (const Clause *) const;
  void dump_clause (const DrupperClause *) const;
  void dump_clause (const vector<int> &) const;
  void dump_chain (ChainDerivation &) const;
  void dump_proof () const;
  void dump_trail () const;

  void trim_ ();
  bool traverse_core (CoreIterator &);
  bool traverse_core (CoreIterator &) const;

  // Interpolation
  //
  unsigned max_color : 16;
  ColorRange analyzed_range;

  void assign_color_range (const vector<int> &) const;

  bool unit (Clause *) const;
  bool shared (Clause *) const;
  bool color_ordered_propagate (bool core = false);
  bool propagate (bool core = false);
  Clause *recursively_colorize (Clause *);
  ChainDerivation colorize (Clause *, int, vector<int> &,
                 ColorRange &);
  bool skip_derivation (Clause *);
  void optimize_proof (vector<Clause *> &);
  void label_initial (ResolutionProofIterator &, int &, ChainDerivation &);
  void label_final (ResolutionProofIterator &, Clause *);
  void replay (ResolutionProofIterator &);

  struct {

    int64_t trims = 0;     // number of trim calls
    int64_t derived = 0;   // number of added derived clauses
    int64_t deleted = 0;   // number of deleted clauses
    int64_t revived = 0;   // number of revived clauses
    int64_t units = 0;     // number of unit clauses allcoated
    int64_t optimized = 0; // number of lemmas in optimized proof

    typedef struct {
      int64_t clauses = 0, lemmas = 0, variables = 0;
    } core_stats;

    core_stats core;               // core statistics in current trim
    vector<core_stats> core_phase; // core statistics per trim phase

    void save_core_phase () {
      core_phase.push_back ({core.clauses, core.lemmas, core.variables});
    }

  } stats;

  bool setup_internal_options ();

  struct Settings {
    bool core_units : 1;  // mark trail reason units as core
    bool check_core : 1;  // assert the set of core literals is unsat (under
                          // debug mode only)
    bool unmark_core : 1; // remove core marks after trim (useful for
                          // testing)
    bool reconstruct : 1; // reconstruct the solver state after trim
    bool report : 1;      // report 'm' and 'M'
    bool optimize_proof : 1; // replace the replayed proof with the new
                             // optimized proof
    bool ordered_propagate;  // replace the replayed proof with the new
                             // optimized proof

    Settings () { // default
      core_units = false;
      check_core = true;
      unmark_core = true;
      report = false;
      optimize_proof = true;
      ordered_propagate = false;
    }

  } settings;

public:
  Drupper (Internal *);
  ~Drupper ();

  void set (const char *, bool val = true);

  void add_derived_clause (Clause *);
  void add_derived_unit_clause (int, bool original = false);
  void add_derived_empty_clause ();
  void add_falsified_original_clause (const vector<int> &, bool);
  void add_failing_assumption (const vector<int> &);
  void add_updated_clause (Clause *);

  void delete_clause (const vector<int> &, bool original = false);
  void delete_clause (Clause *);

  void deallocate_clause (Clause *);

  void update_moved_counterparts ();

  void trim (CoreIterator &);
  void prefer_core_watches (int);

  void pick_new_color (int c = 0);

  void assign_color_range (Clause *) const;
  void assign_color_range (int) const;

  void init_analyzed_color_range (const Clause *c = 0);
  void join_analyzed_color_range (int);
  void join_analyzed_color_range (const Clause *);
  void add_analyzed_color_range (Clause *c = 0);

  void interpolate (ResolutionProofIterator &);
  void trace_check (const char *);

  void print_stats ();
};

} // namespace CaDiCaL

#endif
