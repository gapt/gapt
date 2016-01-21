%------------------------------------------------------------------------------
% File       : E---1.9
% Problem    : RNG103+2 : TPTP v6.2.0. Released v4.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --auto-schedule --tstp-format -s --proof-object --memory-limit=2048 --cpu-limit=%d %s

% Computer   : n189.star.cs.uiowa.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2609 0 2.40GHz
% Memory     : 32286.75MB
% OS         : Linux 2.6.32-504.16.2.el6.x86_64
% CPULimit   : 300s
% DateTime   : Mon May 18 09:52:09 EDT 2015

% Result     : Theorem 0.02s
% Output     : CNFRefutation 0.02s
% Verified   : 
% Statistics : Number of formulae       :   16 (  18 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    4
%              Number of atoms          :   33 (  37 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(c_0_0,axiom,(
    ! [X1,X2,X3] :
      ( ( aElement0(X1)
        & aElement0(X2)
        & aElement0(X3) )
     => ( sdtasdt0(X1,sdtpldt0(X2,X3)) = sdtpldt0(sdtasdt0(X1,X2),sdtasdt0(X1,X3))
        & sdtasdt0(sdtpldt0(X2,X3),X1) = sdtpldt0(sdtasdt0(X2,X1),sdtasdt0(X3,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',mAMDistr)).

fof(c_0_1,hypothesis,
    ( aElement0(xv)
    & sdtasdt0(xc,xv) = xy ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',m__1979)).

fof(c_0_2,hypothesis,(
    aElement0(xc) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',m__1905)).

fof(c_0_3,conjecture,(
    sdtpldt0(xx,xy) = sdtasdt0(xc,sdtpldt0(xu,xv)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',m__)).

fof(c_0_4,hypothesis,
    ( aElement0(xu)
    & sdtasdt0(xc,xu) = xx ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',m__1956)).

fof(c_0_5,plain,(
    ! [X4,X5,X6] :
      ( ( sdtasdt0(X4,sdtpldt0(X5,X6)) = sdtpldt0(sdtasdt0(X4,X5),sdtasdt0(X4,X6))
        | ~ aElement0(X4)
        | ~ aElement0(X5)
        | ~ aElement0(X6) )
      & ( sdtasdt0(sdtpldt0(X5,X6),X4) = sdtpldt0(sdtasdt0(X5,X4),sdtasdt0(X6,X4))
        | ~ aElement0(X4)
        | ~ aElement0(X5)
        | ~ aElement0(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_0])])])).

cnf(c_0_6,plain,
    ( sdtasdt0(X3,sdtpldt0(X2,X1)) = sdtpldt0(sdtasdt0(X3,X2),sdtasdt0(X3,X1))
    | ~ aElement0(X1)
    | ~ aElement0(X2)
    | ~ aElement0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_7,hypothesis,
    ( sdtasdt0(xc,xv) = xy ),
    inference(split_conjunct,[status(thm)],[c_0_1])).

cnf(c_0_8,hypothesis,
    ( aElement0(xc) ),
    inference(split_conjunct,[status(thm)],[c_0_2])).

cnf(c_0_9,hypothesis,
    ( aElement0(xv) ),
    inference(split_conjunct,[status(thm)],[c_0_1])).

fof(c_0_10,negated_conjecture,(
    sdtpldt0(xx,xy) != sdtasdt0(xc,sdtpldt0(xu,xv)) ),
    inference(fof_simplification,[status(thm)],[inference(assume_negation,[status(cth)],[c_0_3])])).

cnf(c_0_11,hypothesis,
    ( sdtpldt0(sdtasdt0(xc,X1),xy) = sdtasdt0(xc,sdtpldt0(X1,xv))
    | ~ aElement0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8]),c_0_9])])).

cnf(c_0_12,hypothesis,
    ( sdtasdt0(xc,xu) = xx ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,hypothesis,
    ( aElement0(xu) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,negated_conjecture,
    ( sdtpldt0(xx,xy) != sdtasdt0(xc,sdtpldt0(xu,xv)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,hypothesis,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])]),c_0_14]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.02  % Problem    : RNG103+2 : TPTP v6.2.0. Released v4.0.0.
% 0.00/0.03  % Command    : eprover --auto-schedule --tstp-format -s --proof-object --memory-limit=2048 --cpu-limit=%d %s
% 0.02/1.06  % Computer   : n189.star.cs.uiowa.edu
% 0.02/1.06  % Model      : x86_64 x86_64
% 0.02/1.06  % CPU        : Intel(R) Xeon(R) CPU E5-2609 0 @ 2.40GHz
% 0.02/1.06  % Memory     : 32286.75MB
% 0.02/1.06  % OS         : Linux 2.6.32-504.16.2.el6.x86_64
% 0.02/1.06  % CPULimit   : 300
% 0.02/1.06  % DateTime   : Sun May 17 10:19:22 CDT 2015
% 0.02/1.06  % CPUTime    : 
% 0.02/1.07  # No SInE strategy applied
% 0.02/1.07  # Trying AutoSched0 for 151 seconds
% 0.02/1.09  # AutoSched0-Mode selected heuristic G_E___200_C41_F1_AE_CS_SP_PI_S0Y
% 0.02/1.09  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.02/1.09  #
% 0.02/1.09  
% 0.02/1.09  # Proof found!
% 0.02/1.09  # SZS status Theorem
% 0.02/1.09  # SZS output start CNFRefutation.
% 0.02/1.09  fof(c_0_0, axiom, (![X1]:![X2]:![X3]:(((aElement0(X1)&aElement0(X2))&aElement0(X3))=>(sdtasdt0(X1,sdtpldt0(X2,X3))=sdtpldt0(sdtasdt0(X1,X2),sdtasdt0(X1,X3))&sdtasdt0(sdtpldt0(X2,X3),X1)=sdtpldt0(sdtasdt0(X2,X1),sdtasdt0(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', mAMDistr)).
% 0.02/1.09  fof(c_0_1, hypothesis, ((aElement0(xv)&sdtasdt0(xc,xv)=xy)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', m__1979)).
% 0.02/1.09  fof(c_0_2, hypothesis, (aElement0(xc)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', m__1905)).
% 0.02/1.09  fof(c_0_3, conjecture, (sdtpldt0(xx,xy)=sdtasdt0(xc,sdtpldt0(xu,xv))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', m__)).
% 0.02/1.09  fof(c_0_4, hypothesis, ((aElement0(xu)&sdtasdt0(xc,xu)=xx)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', m__1956)).
% 0.02/1.09  fof(c_0_5, plain, (![X4]:![X5]:![X6]:((sdtasdt0(X4,sdtpldt0(X5,X6))=sdtpldt0(sdtasdt0(X4,X5),sdtasdt0(X4,X6))|((~aElement0(X4)|~aElement0(X5))|~aElement0(X6)))&(sdtasdt0(sdtpldt0(X5,X6),X4)=sdtpldt0(sdtasdt0(X5,X4),sdtasdt0(X6,X4))|((~aElement0(X4)|~aElement0(X5))|~aElement0(X6))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_0])])])).
% 0.02/1.09  cnf(c_0_6,plain,(sdtasdt0(X3,sdtpldt0(X2,X1))=sdtpldt0(sdtasdt0(X3,X2),sdtasdt0(X3,X1))|~aElement0(X1)|~aElement0(X2)|~aElement0(X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.02/1.09  cnf(c_0_7,hypothesis,(sdtasdt0(xc,xv)=xy), inference(split_conjunct,[status(thm)],[c_0_1])).
% 0.02/1.09  cnf(c_0_8,hypothesis,(aElement0(xc)), inference(split_conjunct,[status(thm)],[c_0_2])).
% 0.02/1.09  cnf(c_0_9,hypothesis,(aElement0(xv)), inference(split_conjunct,[status(thm)],[c_0_1])).
% 0.02/1.09  fof(c_0_10, negated_conjecture, (sdtpldt0(xx,xy)!=sdtasdt0(xc,sdtpldt0(xu,xv))), inference(fof_simplification,[status(thm)],[inference(assume_negation,[status(cth)],[c_0_3])])).
% 0.02/1.09  cnf(c_0_11,hypothesis,(sdtpldt0(sdtasdt0(xc,X1),xy)=sdtasdt0(xc,sdtpldt0(X1,xv))|~aElement0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6, c_0_7]), c_0_8]), c_0_9])])).
% 0.02/1.09  cnf(c_0_12,hypothesis,(sdtasdt0(xc,xu)=xx), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.02/1.09  cnf(c_0_13,hypothesis,(aElement0(xu)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.02/1.09  cnf(c_0_14,negated_conjecture,(sdtpldt0(xx,xy)!=sdtasdt0(xc,sdtpldt0(xu,xv))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.02/1.09  cnf(c_0_15,hypothesis,($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])]), c_0_14]), ['proof']).
% 0.02/1.09  # SZS output end CNFRefutation.
%------------------------------------------------------------------------------
