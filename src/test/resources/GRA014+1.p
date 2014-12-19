%------------------------------------------------------------------------------
% File     : GRA014+1 : TPTP v5.4.0. Released v3.2.0.
% Domain   : Graph Theory
% Problem  : 2-colored completed graph size 6 without subgraph of size 3
% Version  : Especial.
% English  : Find a 2-colored completed graph of size 6 without a complete
%            subgraph of size 3 which all the edges have the same color.

% Refs     : [Bez05] Bezem (2005), Email to Geoff Sutcliffe
% Source   : [Bez05]
% Names    : r3_6 [Bez05]

% Status   : Theorem
% Rating   : 0.00 v5.3.0, 0.18 v5.2.0, 0.00 v4.1.0, 0.11 v4.0.0, 0.10 v3.7.0, 0.33 v3.5.0, 0.12 v3.4.0, 0.08 v3.3.0, 0.00 v3.2.0

% Syntax   : Number of formulae    :    6 (   1 unit)
%            Number of atoms       :   20 (   0 equality)
%            Maximal formula depth :    7 (   5 average)
%            Number of connectives :   14 (   0 ~  ;   1  |;   9  &)
%                                         (   0 <=>;   4 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    4 (   1 propositional; 0-2 arity)
%            Number of functors    :    6 (   6 constant; 0-0 arity)
%            Number of variables   :   11 (   0 singleton;  11 !;   0 ?)
%            Maximal term depth    :    1 (   1 average)
% SPC      : FOF_THM_EPR

% Comments :
%------------------------------------------------------------------------------
fof(red_clique,axiom,(
    ! [A,B,C] :
      ( ( red(A,B)
        & red(B,C)
        & red(A,C) )
     => goal ) )).

fof(green_clique,axiom,(
    ! [A,B,C] :
      ( ( green(A,B)
        & green(B,C)
        & green(A,C) )
     => goal ) )).

fof(ordering,axiom,
    ( less_than(n1,n2)
    & less_than(n2,n3)
    & less_than(n3,n4)
    & less_than(n4,n5)
    & less_than(n5,n6) )).

fof(less_than_transitive,axiom,(
    ! [A,B,C] :
      ( ( less_than(A,B)
        & less_than(B,C) )
     => less_than(A,C) ) )).

fof(partition,axiom,(
    ! [A,B] :
      ( less_than(A,B)
     => ( red(A,B)
        | green(A,B) ) ) )).

fof(goal_to_be_proved,conjecture,(
    goal )).
%------------------------------------------------------------------------------
