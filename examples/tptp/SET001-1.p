%--------------------------------------------------------------------------
% File     : SET001-1 : TPTP v6.3.0. Released v1.0.0.
% Domain   : Set Theory
% Problem  : Set members are superset members
% Version  : [LS74] axioms.
% English  : A member of a set is also a member of that set's supersets.

% Refs     : [LS74]  Lawrence & Starkey (1974), Experimental Tests of Resol
%          : [WM76]  Wilson & Minker (1976), Resolution, Refinements, and S
% Source   : [SPRFN]
% Names    : ls100 [LS74]
%          : ls100 [WM76]

% Status   : Unsatisfiable
% Rating   : 0.00 v2.0.0
% Syntax   : Number of clauses     :    9 (   1 non-Horn;   3 unit;   8 RR)
%            Number of atoms       :   17 (   0 equality)
%            Maximal clause size   :    3 (   2 average)
%            Number of predicates  :    3 (   0 propositional; 2-2 arity)
%            Number of functors    :    4 (   3 constant; 0-2 arity)
%            Number of variables   :   13 (   0 singleton)
%            Maximal term depth    :    2 (   1 average)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments :
%--------------------------------------------------------------------------
%----Include the member and subset axioms
%--------------------------------------------------------------------------
cnf(membership_in_subsets,axiom,
    ( ~ member(Element,Subset)
    | ~ subset(Subset,Superset)
    | member(Element,Superset) )).

cnf(subsets_axiom1,axiom,
    ( subset(Subset,Superset)
    | member(member_of_1_not_of_2(Subset,Superset),Subset) )).

cnf(subsets_axiom2,axiom,
    ( ~ member(member_of_1_not_of_2(Subset,Superset),Superset)
    | subset(Subset,Superset) )).

cnf(set_equal_sets_are_subsets1,axiom,
    ( ~ equal_sets(Subset,Superset)
    | subset(Subset,Superset) )).

cnf(set_equal_sets_are_subsets2,axiom,
    ( ~ equal_sets(Superset,Subset)
    | subset(Subset,Superset) )).

cnf(subsets_are_set_equal_sets,axiom,
    ( ~ subset(Set1,Set2)
    | ~ subset(Set2,Set1)
    | equal_sets(Set2,Set1) )).

%--------------------------------------------------------------------------
%--------------------------------------------------------------------------
cnf(b_equals_bb,hypothesis,
    ( equal_sets(b,bb) )).

cnf(element_of_b,hypothesis,
    ( member(element_of_b,b) )).

cnf(prove_element_of_bb,negated_conjecture,
    ( ~ member(element_of_b,bb) )).

%--------------------------------------------------------------------------
