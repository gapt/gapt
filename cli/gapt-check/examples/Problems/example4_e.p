%------------------------------------------------------------------------------
% File     : example4_e : ProoVer 2026
% Source   : ProoVer 2026
% Status   : Unknown
% SPC      : FOF_UNK_RFO_NEQ
%------------------------------------------------------------------------------
% SZS output start ListOfFormulae
%----At every marriage, there is a bride and groom who are in love
fof(marriage, axiom,
    ! [Marriage] :
    ? [Bride] :
    ? [Groom] :
    in_love(Groom, Bride)).

%----Conjecture: someone is in love
fof(c, conjecture,
    ? [X] :
    ? [Y] :
    in_love(X, Y)).
% SZS output end ListOfFormulae
