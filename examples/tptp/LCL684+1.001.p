%------------------------------------------------------------------------------
% File     : LCL684+1.001 : TPTP v7.2.0. Released v4.0.0.
% Domain   : Logic Calculi (Modal Logic)
% Problem  : In S4, pigeonhole formulae, size 1
% Version  : Especial.
% English  :

% Refs     : [BHS00] Balsiger et al. (2000), A Benchmark Method for the Pro
%          : [Kam08] Kaminski (2008), Email to G. Sutcliffe
% Source   : [Kam08]
% Names    : s4_ph_p [BHS00]

% Status   : Theorem
% Rating   : 0.00 v5.3.0, 0.09 v5.2.0, 0.00 v4.1.0, 0.06 v4.0.1, 0.05 v4.0.0
% Syntax   : Number of formulae    :    3 (   1 unit)
%            Number of atoms       :   10 (   0 equality)
%            Maximal formula depth :   12 (   7 average)
%            Number of connectives :   14 (   7   ~;   3   |;   3   &)
%                                         (   0 <=>;   1  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    3 (   0 propositional; 1-2 arity)
%            Number of functors    :    0 (   0 constant; --- arity)
%            Number of variables   :    7 (   0 sgn;   6   !;   1   ?)
%            Maximal term depth    :    1 (   1 average)
% SPC      : FOF_THM_EPR

% Comments : A naive relational encoding of the modal logic problem into
%            first-order logic.
%------------------------------------------------------------------------------
fof(reflexivity,axiom,(
    ! [X] : r1(X,X) )).

fof(transitivity,axiom,(
    ! [X,Y,Z] :
      ( ( r1(X,Y)
        & r1(Y,Z) )
     => r1(X,Z) ) )).

fof(main,conjecture,(
    ~ ( ? [X] :
          ~ ( ~ ( ! [Y] :
                    ( ~ r1(X,Y)
                    | ! [X] :
                        ( ~ r1(Y,X)
                        | ~ ( p201(X)
                            & p101(X) ) ) ) )
            | ~ ( p201(X)
                & p101(X) ) ) ) )).

%------------------------------------------------------------------------------
