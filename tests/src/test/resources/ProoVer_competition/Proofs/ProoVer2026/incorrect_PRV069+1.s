%------------------------------------------------------------------------------
% File     : PRV069+1.s : ProoVer 2026
% Proof    : Problems/PRV069+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    ( pp(sK0)
    & pp(sK1)
    & pp(esk1_0)
    & pp('$c1')
    & qq(esk2_1(sK0))
    & qq('$f1'(esk1_0))
    & esk3_0(sK1)
    & ! [ESK1_0] :
        ( qq(ESK1_0)
        | ~ qq(ESK1_0) ) ),
    file('Problems/PRV069+1.p',a1) ).

fof(c,conjecture,
    ! [SK0] : pp(SK0),
    file('Problems/PRV069+1.p',c) ).

fof(s,plain,
    ! [SK0] : pp(SK0),
    inference(over_generalize,[status(thm)],[a1]) ).

fof(negc,negated_conjecture,
    ~ ! [SK0] : pp(SK0),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[negc,s]) ).

% SZS output end Proof
