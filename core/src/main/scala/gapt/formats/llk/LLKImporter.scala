package gapt.formats.llk

import gapt.proofs.HOLSequent
import gapt.formats.llk.ast.LambdaAST
import gapt.expr.hol._
import gapt.expr._
import gapt.expr.BetaReduction._
import gapt.proofs.lk._

import scala.annotation.tailrec
import EquationVerifier._
import gapt.utils.Logger

private object LLKLogger extends Logger( "llk" ); import LLKLogger._

object LLKFormatter {
  /* formats a sequent */
  def f( fs: HOLSequent ): String = {
    " " + fs.antecedent.map( toLLKString.apply ).mkString( ", " ) + " :- " +
      fs.succedent.map( toLLKString.apply ).mkString( ", " ) + " "
  }

  def f( s: Substitution ): String = {
    s.map.map( x => f( x._1 ) + " -> " + f( x._2 ) ).mkString( "{", ",", "}" )
  }

  def f( e: Expr ): String = " " + toLLKString( e ) + " "
}

/**
 * This implements the second parsing pass, converting hlk Tokens to an LK Proof. HybridLatexParser inherits from
 * TokenToLKConverter to have a common interface, but the code here is only dependent on the AST. It uses the ASTtoHOL
 * object to create Exprs from hol ASTs.
 */
trait TokenToLKConverter {
  import LLKFormatter._

  /* Extracts type declarations from the tokens and creates a function to create atomic terms by name */
  def createNaming( r: List[Token] ): ( String => Expr ) = {
    val ctypes: List[( String, Ty )] = r.flatMap( _ match {
      case TToken( "CONST", names, t ) => names map ( ( _, t ) )
      case _                           => Nil
    } )
    val constmap = Map[String, Ty]() ++ ctypes

    val vtypes: List[( String, Ty )] = r.flatMap( _ match {
      case TToken( "VAR", names, t ) => names map ( ( _, t ) )
      case _                         => Nil
    } )
    val varmap = Map[String, Ty]() ++ vtypes

    { ( s: String ) =>
      {
        if ( varmap contains s ) {
          Var( s, varmap( s ) )
        } else if ( constmap contains s ) {
          Const( s, constmap( s ) )
        } else

          throw new HybridLatexParserException( "no type declaration for symbol " + s )
      }
    }
  }

  def printRules( r: List[Token] ): List[HOLSequent] = {
    val rules = r.filter( _ match { case RToken( _, _, _, _, _ ) => true; case _ => false } )
    val naming = createNaming( r )

    var l = List[HOLSequent]()

    for ( RToken( name, argname, antecedent, succedent, _ ) <- rules ) {
      val ant = antecedent.map( x => c( LLKFormulaParser.ASTtoHOL( naming, x ) ) )
      val suc = succedent.map( x => c( LLKFormulaParser.ASTtoHOL( naming, x ) ) )
      val fs = HOLSequent( ant, suc )
      //println(name + ": "+fs)
      l = fs :: l
    }

    l.reverse
  }

  /* The main entry point to the proof parser. The list of tokens l is taken apart into subproofs (noticable by the
     CONTINUEWITH rule). Then the subproofs are ordered by dependency and constructed in this order*/
  def createLKProof( l: List[Token] ): ExtendedProofDatabase = {
    //seperate rule tokens from type declaration tokens
    val ( rtokens, tatokens ) = l.partition {
      case RToken( _, _, _, _, _ ) => true;
      case _                       => false;
    }.asInstanceOf[( List[RToken], List[Token] )] //need to cast because partition returns Tokens
    val ( ttokens, atokens ) = tatokens.partition {
      case TToken( _, _, _ )        => true;
      case t @ AToken( _, _, _, _ ) => false;
      case t: Token => throw new Exception(
        "Severe error: rule tokens were already filtered out, but rule " + t + " still contained!" )
    }.asInstanceOf[( List[TToken], List[AToken] )] //need to cast because partition returns Tokens
    //println("creating naming!")
    val naming = createNaming( ttokens )
    //println("creating axioms!")
    val unclosedaxioms = createAxioms( naming, atokens )
    //println("closing axioms!")
    val axioms = unclosedaxioms map ( x => ( x._1, universalClosure( x._2 ) ) )
    //println(axioms)
    //println("creating definitions!")
    val llk_definitions = createDefinitions( naming, atokens, axioms )

    //println(definitions)
    //seperate inferences for the different (sub)proofs
    val ( last, rm ) = rtokens.foldLeft( List[RToken](), Map[Formula, List[RToken]]() )( ( current, token ) => {
      token match {
        case RToken( "CONTINUEWITH", Some( name ), a, s, _ ) =>
          //put proof under name into map, continue with empty rulelist
          try {
            val nformula = c( LLKFormulaParser.ASTtoHOL( naming, name ) )
            ( Nil, current._2 + ( ( nformula, current._1.reverse ) ) )
          } catch {
            case e: Exception => throw new HybridLatexParserException(
              "Error in parsing CONTINUEWITH{" + name + "}{" + a + "}{" + s"}: " + e.getMessage, e )
          }
        case RToken( "CONTINUEWITH", _, _, _, _ ) =>
          throw new HybridLatexParserException( "The CONTINUEWITH statement needs a name giving the argument!" )
        case RToken( "COMMENT", _, _, _, _ ) =>
          //filter comments
          current
        case _ =>
          //apend rule to current list
          ( token :: current._1, current._2 )
      }
    } )

    require(
      last.isEmpty,
      "There are some rules left after parsing the list, use CONTINUEFROM to give proof a name! " + last )

    //dependncy analysis
    val dependecies = getDependecyMap( naming, rm )
    val ordering: List[Formula] = getOrdering( dependecies )

    //proof completion in dependency order
    val proofs = ordering.foldLeft( Map[Formula, LKProof]() )( ( proofs_done, f ) => {
      //println("Processing (sub)proof "+this.f(f))
      val f_proof: LKProof = completeProof( f, proofs_done, naming, rm( f ), axioms, llk_definitions )
      proofs_done + ( ( f, f_proof ) )
    } )
    ExtendedProofDatabase( proofs, axioms, llk_definitions.map( d =>
      llkDefinitionToLKDefinition( d._1, d._2 ).toTuple ) )
  }

  /* Creates the subproof proofname from a list of rules. Uses the naming function to create basic term and
  *  uses the proofs map to look up subproofs referenced by CONTINUEWITH and INSTLEMMA. This means, the calls
  *  to completeProof have to be ordered s.t. dependent proofs are already contained in the map.*/
  def completeProof(
    proofname:   Formula,
    proofs:      Map[Formula, LKProof],
    naming:      String => Expr,
    rules:       List[RToken],
    axioms:      Map[Formula, Formula],
    definitions: Map[Expr, Expr] ): LKProof = {
    var proofstack: List[LKProof] = List[LKProof]()
    for ( rt @ RToken( name, auxterm, antecedent, succedent, sub ) <- rules ) {
      //println("Processing rule: "+name)
      val ant = antecedent.map( x => c( LLKFormulaParser.ASTtoHOL( naming, x ) ) )
      val suc = succedent.map( x => c( LLKFormulaParser.ASTtoHOL( naming, x ) ) )
      val fs = HOLSequent( ant, suc )
      val nLine = sys.props( "line.separator" )
      name match {
        case "AX" =>
          val expaxiom = ( ant, suc ) match {
            case _ if ant == suc => //this is a workaround for the more restricted lk introduction rules
              AtomicExpansion( ant.head ) //TODO: remove atomic expansion when it's not necessary anymore
            case _ =>
              ProofLink( FOLAtom( "llkAxiom" ), HOLSequent( ant, suc ) )
          }
          proofstack = expaxiom :: proofstack
          require(
            proofstack.nonEmpty && proofstack.head.endSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) +
              " got " + f( proofstack.head.endSequent ) + " instead!" )
        case "TAUTCOMPLETION" =>
          require(
            ant.size == 1,
            "Tautological Axiom Completion needs exactly one formula in the antecedent, not " + ant.mkString( "," ) )
          require( suc.size == 1, "Tautological Axiom Completion needs exactly one formula in the succedent, not "
            + suc.mkString( "," ) )
          require(
            ant.head == suc.head,
            "Tautological Axiom Completion can only expand sequents of the form F :- F, not " +
              HOLSequent( ant, suc ) )
          val rule = AtomicExpansion( ant.head )
          proofstack = rule :: proofstack
          require(
            proofstack.nonEmpty && proofstack.head.endSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) +
              " got " + f( proofstack.head.endSequent ) + " instead!" )
        case "AUTOPROP" =>
          try {
            val Right( rule ) = solvePropositional( HOLSequent( ant, suc ) )
            proofstack = rule :: proofstack
            require(
              proofstack.nonEmpty && proofstack.head.endSequent.multiSetEquals( fs ),
              "Error creating rule! Expected sequent: " + f( fs ) +
                " got " + f( proofstack.head.endSequent ) + " instead!" )
          } catch {
            case e: Exception =>
              throw new HybridLatexParserException(
                "Autopropositional failed with the message: " + e.getMessage + nLine + "Stack Trace:" + nLine +
                  e.getStackTrace.mkString( "", nLine, nLine ), e )
          }
        // --- quantifier rules ---
        case "ALLL" =>
          proofstack = handleWeakQuantifier( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack.head.endSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) +
              " got " + f( proofstack.head.endSequent ) + " instead!" )
        case "EXR" =>
          proofstack = handleWeakQuantifier( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack.head.endSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) +
              " got " + f( proofstack.head.endSequent ) + " instead!" )
        case "ALLR" =>
          proofstack = handleStrongQuantifier( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack.head.endSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) +
              " got " + f( proofstack.head.endSequent ) + " instead!" )
        case "EXL" =>
          proofstack = handleStrongQuantifier( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack.head.endSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) +
              " got " + f( proofstack.head.endSequent ) + " instead!" )
        case "ANDR" =>
          proofstack = handleBinaryLogicalOperator( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack.head.endSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) +
              " got " + f( proofstack.head.endSequent ) + " instead!" )
        case "ORL" =>
          proofstack = handleBinaryLogicalOperator( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack.head.endSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) +
              " got " + f( proofstack.head.endSequent ) + " instead!" )
        case "IMPL" =>
          proofstack = handleBinaryLogicalOperator( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack.head.endSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) +
              " got " + f( proofstack.head.endSequent ) + " instead!" )
        // --- unary rules ---
        case "ORR" =>
          proofstack = handleUnaryLogicalOperator( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack.head.endSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) +
              " got " + f( proofstack.head.endSequent ) + " instead!" )
        case "ANDL" =>
          proofstack = handleUnaryLogicalOperator( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack.head.endSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) +
              " got " + f( proofstack.head.endSequent ) + " instead!" )
        case "IMPR" =>
          proofstack = handleUnaryLogicalOperator( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack.head.endSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) +
              " got " + f( proofstack.head.endSequent ) + " instead!" )
        // --- negation rules ---
        case "NEGL" =>
          proofstack = handleNegation( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack.head.endSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) +
              " got " + f( proofstack.head.endSequent ) + " instead!" )
        case "NEGR" =>
          proofstack = handleNegation( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack.head.endSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) +
              " got " + f( proofstack.head.endSequent ) + " instead!" )

        // --- equational rules ---
        case "EQL" =>
          proofstack = handleEquality( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack.head.endSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) +
              " got " + f( proofstack.head.endSequent ) + " instead!" )
        case "EQR" =>
          proofstack = handleEquality( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack.head.endSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) +
              " got " + f( proofstack.head.endSequent ) + " instead!" )

        // --- definition rules ---
        case "DEF" =>
          proofstack = handleDefinitions( proofstack, name, fs, auxterm, naming, rt, definitions )
          require(
            proofstack.nonEmpty && proofstack.head.endSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) +
              " got " + f( proofstack.head.endSequent ) + " instead!" )

        // --- structural rules ---
        case "CONTRL" =>
          proofstack = handleContraction( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack.head.endSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) +
              " got " + f( proofstack.head.endSequent ) + " instead!" )
        case "CONTRR" =>
          proofstack = handleContraction( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack.head.endSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) +
              " got " + f( proofstack.head.endSequent ) + " instead!" )
        case "WEAKL" =>
          proofstack = handleWeakening( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack.head.endSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) +
              " got " + f( proofstack.head.endSequent ) + " instead!" )
        case "WEAKR" =>
          proofstack = handleWeakening( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack.head.endSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) +
              " got " + f( proofstack.head.endSequent ) + " instead!" )
        case "CUT" =>
          proofstack = handleCut( proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack.head.endSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) +
              " got " + f( proofstack.head.endSequent ) + " instead!" )

        // --- macro rules ---
        case "EQAXIOM" =>
          proofstack = handleEQAxiom( proofstack, name, fs, auxterm, sub, naming, rt, axioms, definitions )
          require(
            proofstack.nonEmpty && proofstack.head.endSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) +
              " got " + f( proofstack.head.endSequent ) + " instead!" )

        case "INSTAXIOM" =>
          proofstack = handleInstAxiom( proofstack, name, fs, auxterm, sub, naming, rt, axioms, definitions )
          require(
            proofstack.nonEmpty && proofstack.head.endSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) +
              " got " + f( proofstack.head.endSequent ) + " instead!" )

        case "CONTINUEFROM" =>
          proofstack = handleLink( proofs, proofstack, name, fs, auxterm, naming, rt )
          require(
            proofstack.nonEmpty && proofstack.head.endSequent.multiSetEquals( fs ),
            "Error creating rule! Expected sequent: " + f( fs ) +
              " got " + f( proofstack.head.endSequent ) + " instead!" )
        case "CONTINUEWITH" => ;
        case "COMMENT"      => ;
        case _              => throw new HybridLatexParserException( "Rule type " + name + " not yet implemented!" )
      }

    }

    require( proofstack.nonEmpty, "Error creating proof: Proof stack may not be empty!" )
    proofstack.head
  }

  /* Takes care of weak quantifiers. */
  def handleWeakQuantifier( current_proof: List[LKProof], ruletype: String,
                            fs: HOLSequent, auxterm: Option[LambdaAST],
                            naming: ( String ) => Expr, rt: RToken ): List[LKProof] = {
    require( current_proof.nonEmpty, "Imbalanced proof tree in application of " + ruletype + " with es: " + fs )
    val oldproof :: rest = current_proof

    val ( mainsequent, auxsequent, _ ) = filterContext( oldproof.endSequent, fs )
    require(
      auxsequent.formulas.size == 1,
      "Exactly one auxiliary formula in weak quantifier rule required (no autocontraction allowed)! " + auxsequent )
    val ( main, aux ) = ruletype match {
      //TODO: if you use ALLL instead of ALLR, you might get an index out of bounds exception!
      case "ALLL" => ( mainsequent.antecedent.head, auxsequent.antecedent.head )
      case "EXR"  => ( mainsequent.succedent.head, auxsequent.succedent.head )
    }

    def inferTerm( x: Var, holf: Formula ): Expr = {
      syntacticMatching( holf, aux ) match {
        case Some( sub ) =>
          val s: Expr = sub.map.getOrElse( x, x )
          //in case the variable was projected away, we use the identity function
          if ( auxterm.nonEmpty ) {
            //try to use user provided term
            val t: Expr = LLKFormulaParser.ASTtoHOL( naming, auxterm.get )
            if ( s == t ) {
              // println("Remark: automatically inferred the auxiliaray term " + f(t) + " in formula "+f(f))
              t
            } else {
              debug( "Preferring user specified term " + f( t ) + " over inferred term " + f( s ) + "." )
              t
            }
          } else {
            //no user provided term
            s
          }

        case None =>
          //          println("Remark: Could not infer substitution term, using user specified one!")
          LLKFormulaParser.ASTtoHOL( naming, auxterm.getOrElse(
            throw new HybridLatexParserException( "No substitution term found, please specify! " + rt ) ) )
      }
    }

    main match {
      case All( x, f ) =>
        require( ruletype == "ALLL", "Main formula " + main + " can not be used in a forall left rule!" )
        val term = inferTerm( x, f )
        val rule = ForallLeftRule( oldproof, main, term )
        rule :: rest

      case Ex( x, f ) =>
        inferTerm( x, f )
        require( ruletype == "EXR", "Main formula " + main + " can not be used in a exists right rule!" )
        val term = inferTerm( x, f )
        val rule = ExistsRightRule( oldproof, main, term )
        rule :: rest
    }
  }

  def handleStrongQuantifier( current_proof: List[LKProof], ruletype: String,
                              fs: HOLSequent, auxterm: Option[LambdaAST],
                              naming: ( String ) => Expr, rt: RToken ): List[LKProof] = {
    require( current_proof.nonEmpty, "Imbalanced proof tree in application of " + ruletype + " with es: " + fs )
    val oldproof = current_proof.head
    val ( mainsequent, auxsequent, _ ) = filterContext( oldproof.endSequent, fs )
    require(
      auxsequent.formulas.size == 1,
      "Exactly one auxiliary formula in strong quantifier rule required! " + auxsequent )
    val ( main, aux ) = ruletype match {
      case "EXL"  => ( mainsequent.antecedent.head, auxsequent.antecedent.head )
      case "ALLR" => ( mainsequent.succedent.head, auxsequent.succedent.head )
    }

    def inferTerm( x: Var, f: Formula ): Expr = {
      syntacticMatching( f, aux ) match {
        case Some( sub ) =>
          val s: Expr = sub.map.getOrElse( x, x ) //in case the term was projected away we try the identity function
          if ( auxterm.nonEmpty ) {
            //try to use user provided term
            val t: Expr = LLKFormulaParser.ASTtoHOL( naming, auxterm.get )
            if ( s == t ) {
              //              println("Remark: automatically inferred the auxiliaray term in rule " + rt + ".")
              require(
                t.isInstanceOf[Var],
                "Strong quantifier rule needs an eigenvariable as argument, but " + t + " is not!" )
              t
            } else {
              debug( "Preferring user specified term " + t + " over inferred term " + s + "." )
              require(
                t.isInstanceOf[Var],
                "Strong quantifier rule needs an eigenvariable as argument, but " + t + " is not!" )
              t
            }
          } else {
            //no user provided term
            // require(s.isInstanceOf[Var],
            //  "Strong quantifier rule needs an eigenvariable as argument, but "+s+" is not!")
            s
          }

        case None =>
          //automatic mode failed
          debug( "Remark: Could not infer substitution term, using user specified one!" )
          val t = LLKFormulaParser.ASTtoHOL( naming, auxterm.getOrElse(
            throw new HybridLatexParserException( "No substitution term found, please specify! " + rt ) ) )
          require(
            t.isInstanceOf[Var],
            "Strong quantifier rule needs an eigenvariable as argument, but " + t + " is not!" )
          t
      }
    }

    main match {
      case All( x, f ) =>
        val v = inferTerm( x, f )
        require( ruletype == "ALLR", "Main formula " + main + " can not be used in a forall right rule!" )
        val rule = ForallRightRule( oldproof, main, v.asInstanceOf[Var] )
        rule :: current_proof.tail

      case Ex( x, f ) =>
        val v = inferTerm( x, f )
        require( ruletype == "EXL", "Main formula " + main + " can not be used in a exists left rule!" )
        val rule = ExistsLeftRule( oldproof, main, v.asInstanceOf[Var] )
        rule :: current_proof.tail
    }
  }

  def handleBinaryLogicalOperator( current_proof: List[LKProof], ruletype: String,
                                   fs: HOLSequent, auxterm: Option[LambdaAST],
                                   naming: ( String ) => Expr, rt: RToken ): List[LKProof] = {
    require( current_proof.size > 1, "Imbalanced proof tree in application of " + ruletype + " with es: " + fs )
    val rightproof :: leftproof :: stack = current_proof

    val ( mainsequent, auxsequent, context ) = filterContext( leftproof.endSequent, rightproof.endSequent, fs )

    try {
      ruletype match {
        case "ANDR" =>
          mainsequent.succedent.head match {
            case And( l, r ) =>
              require(
                auxsequent.succedent.contains( l ),
                "Left branch formula " + l + " not found in auxiliary formulas" + f( auxsequent ) )
              require(
                auxsequent.succedent.contains( r ),
                "Right branch formula " + r + " not found in auxiliary formulas!" + f( auxsequent ) )
              require(
                leftproof.endSequent.succedent.contains( l ),
                "Left branch formula " + l + " not found in auxiliary formulas " + leftproof.endSequent )
              require(
                rightproof.endSequent.succedent.contains( r ),
                "Right branch formula " + r + " not found in auxiliary formulas!" + rightproof.endSequent )
              val inf = AndRightRule( leftproof, l, rightproof, r )
              val contr = ContractionMacroRule( inf, fs )
              contr :: stack
            case _ => throw new HybridLatexParserException(
              "Main formula of a conjunction right rule must have conjuntion as outermost operator!" )
          }

        case "ORL" =>
          mainsequent.antecedent.head match {
            case Or( l, r ) =>
              require(
                auxsequent.antecedent.contains( l ),
                "Left branch formula " + l + " not found in auxiliary formulas " + f( auxsequent ) )
              require(
                auxsequent.antecedent.contains( r ),
                "Right branch formula " + r + " not found in auxiliary formulas!" + f( auxsequent ) )
              require(
                leftproof.endSequent.antecedent.contains( l ),
                "Left branch formula " + l + " not found in auxiliary formulas " + leftproof.endSequent )
              require(
                rightproof.endSequent.antecedent.contains( r ),
                "Right branch formula " + r + " not found in auxiliary formulas!" + rightproof.endSequent )
              val inf = OrLeftRule( leftproof, l, rightproof, r )
              val contr = ContractionMacroRule( inf, fs )
              contr :: stack
            case _ => throw new HybridLatexParserException(
              "Main formula of a disjunction left rule must have disjunction as outermost operator!" )
          }

        case "IMPL" =>
          mainsequent.antecedent.head match {
            case Imp( l, r ) =>
              require(
                auxsequent.succedent.contains( l ),
                "Left branch formula " + l + " not found in auxiliary formulas " + f( auxsequent ) )
              require(
                auxsequent.antecedent.contains( r ),
                "Right branch formula " + r + " not found in auxiliary formulas!" + f( auxsequent ) )
              require(
                leftproof.endSequent.succedent.contains( l ),
                "Left branch formula " + l + " not found in auxiliary formulas " + leftproof.endSequent )
              require(
                rightproof.endSequent.antecedent.contains( r ),
                "Right branch formula " + r + " not found in auxiliary formulas!" + rightproof.endSequent )
              val inf = ImpLeftRule( leftproof, l, rightproof, r )
              val contr = ContractionMacroRule( inf, fs )
              contr :: stack
            case _ => throw new HybridLatexParserException(
              "Main formula of a implication left rule must have implication as outermost operator!" )
          }
      }
    } catch {
      case e: Exception => throw new HybridLatexParserException(
        "Error in handling binary rule with end-sequent: " + f( fs ) + sys.props( "line.separator" ) +
          "Problem: " + e.getMessage, e )
    }
  }

  def handleUnaryLogicalOperator( current_proof: List[LKProof], ruletype: String,
                                  fs: HOLSequent, auxterm: Option[LambdaAST],
                                  naming: ( String ) => Expr, rt: RToken ): List[LKProof] = {
    require( current_proof.nonEmpty, "Imbalanced proof tree in application of " + ruletype + " with es: " + fs )
    val top :: stack = current_proof

    val ( mainsequent, auxsequent, context ) = filterContext( top.endSequent, fs )

    ruletype match {
      case "ORR" =>
        mainsequent.succedent.head match {
          case or @ Or( l, r ) =>
            val inf = ( auxsequent.succedent.contains( l ), auxsequent.succedent.contains( r ) ) match {
              case ( false, false ) =>
                throw new Exception( "Neither " + l + " nor " + r + " found in auxiliary formulas" + f( auxsequent ) )
              case ( false, true ) =>
                OrRightRule( WeakeningRightRule( top, l ), or )
              case ( true, false ) =>
                OrRightRule( WeakeningRightRule( top, r ), or )
              case ( true, true ) =>
                OrRightRule( top, or )
            }

            val contr = ContractionMacroRule( inf, fs, strict = true )
            contr :: stack
          case _ => throw new HybridLatexParserException(
            "Main formula of a disjunction right rule must have conjunction as outermost operator!" )
        }

      case "ANDL" =>
        mainsequent.antecedent.head match {
          case and @ And( l, r ) =>
            val inf = ( auxsequent.antecedent.contains( l ), auxsequent.antecedent.contains( r ) ) match {
              case ( false, false ) =>
                throw new Exception( "Neither " + l + " nor " + r + " found in auxiliary formulas" + f( auxsequent ) )
              case ( false, true ) =>
                AndLeftRule( WeakeningLeftRule( top, l ), and )
              case ( true, false ) =>
                AndLeftRule( WeakeningLeftRule( top, r ), and )
              case ( true, true ) =>
                AndLeftRule( top, and )
            }

            val contr = ContractionMacroRule( inf, fs, strict = true )
            contr :: stack
          case _ => throw new HybridLatexParserException(
            "Main formula of a conjunction left rule must have disjunction as outermost operator!" )
        }

      case "IMPR" =>
        mainsequent.succedent.head match {
          case Imp( l, r ) =>
            require(
              auxsequent.antecedent.contains( l ),
              "Left branch formula " + l + " not found in auxiliary formulas " + f( auxsequent ) )
            require(
              auxsequent.succedent.contains( r ),
              "Right branch formula " + r + " not found in auxiliary formulas!" + f( auxsequent ) )
            require(
              top.endSequent.antecedent.contains( l ),
              "Left branch formula " + l + " not found in auxiliary formulas " + top.endSequent )
            require(
              top.endSequent.succedent.contains( r ),
              "Right branch formula " + r + " not found in auxiliary formulas!" + top.endSequent )
            val inf = ImpRightRule( top, l, r )
            val contr = ContractionMacroRule( inf, fs )
            contr :: stack
          case _ => throw new HybridLatexParserException(
            "Main formula of a implication right rule must have implication as outermost operator!" )
        }
    }
  }

  def handleNegation( current_proof: List[LKProof], ruletype: String,
                      fs: HOLSequent, auxterm: Option[LambdaAST],
                      naming: ( String ) => Expr, rt: RToken ): List[LKProof] = {
    require( current_proof.nonEmpty, "Imbalanced proof tree in application of " + ruletype + " with es: " + fs )
    val top :: stack = current_proof
    val ( main, aux, context ) = filterContext( top.endSequent, fs )

    val left = main.antecedent.foldLeft( top )( ( intermediate, f ) => {
      f match {
        case Neg( g ) =>
          NegLeftRule( intermediate, g )
        case _ =>
          throw new HybridLatexParserException(
            "Trying to apply the negation rule on formula " + f +
              " without negation as outermost symbol on " + top.endSequent + " to get " + fs )
      }
    } )
    val right = main.succedent.foldLeft( left )( ( intermediate, f ) => {
      f match {
        case Neg( g ) =>
          NegRightRule( intermediate, g )
        case _ =>
          throw new HybridLatexParserException(
            "Trying to apply the negation rule on formula " + f +
              " without negation as outermost symbol on " + top.endSequent + " to get " + fs )
      }
    } )

    val contr = ContractionMacroRule( right, fs, strict = false )

    require(
      contr.endSequent multiSetEquals fs,
      "Could not create target sequent " + fs + " by a series of negations from " + top.endSequent +
        " but got " + contr.endSequent + " instead!" )
    contr :: stack
  }

  //TODO: refactor, a lot of code is already done in the rule constructors now
  def handleEquality( current_proof: List[LKProof], ruletype: String,
                      fs: HOLSequent, auxterm: Option[LambdaAST],
                      naming: ( String ) => Expr, rt: RToken ): List[LKProof] = {
    require( current_proof.size > 1, "Imbalanced proof tree in application of " + ruletype + " with es: " + fs )
    val rightproof :: leftproof :: stack = current_proof

    //In the case the main formula is the same as an auxiliariy formula, filterContext cannot infer the main formula
    //we doe this now by hand
    def eqfilter( x: Formula ): Boolean = x match { case Eq( s, t ) => true; case _ => false }
    def canReplace( s: Expr, t: Expr, exp1: Expr, exp2: Expr ): Boolean = {
      ( checkReplacement( s, t, exp1, exp2 ), checkReplacement( t, s, exp1, exp2 ) ) match {
        case ( EqualModuloEquality( _ ), _ ) => true
        case ( _, EqualModuloEquality( _ ) ) => true
        case _                               => false
      }
    }

    val lefteqs = leftproof.endSequent.succedent.filter( eqfilter )
    ruletype match {
      case "EQL" =>
        //we find all candidates, i.e. equations e: s=t in the left parent and pair it with possible formulas f
        // from the right parent together with possible main formulas in the conclusion s.t. f[s] = main[t] or
        // f[t] = main[s]
        val righteqsante = rightproof.endSequent.antecedent
        val candidates = for (
          e @ Eq( s, t ) <- lefteqs;
          f <- righteqsante;
          main <- fs.antecedent;
          if canReplace( s, t, f, main )
        ) yield { ( s, t, e, f, main ) }

        require( candidates.nonEmpty, "For an eq:l rule, could not find a possible replacement of an equation from "
          + lefteqs.map( f( _ ) ).mkString( "(", ",", ")" ) + " in " +
          fs.antecedent.map( f( _ ) ).mkString( "(", ",", ")" ) )

        //now we try to create an inference from each candidate
        val inferences: Seq[LKProof] = candidates.flatMap( args => {
          val ( s, t, eq, f, main ) = args
          val l1 = {
            //we check if we can paramodulate s=t ...
            checkReplacement( s, t, f, main ) match {
              case EqualModuloEquality( _ ) =>
                val rule = CutRule( leftproof, eq,
                  EqualityLeftRule( WeakeningLeftRule( rightproof, eq ), eq, f, main ), eq )
                try {
                  ContractionMacroRule( rule, fs ) :: Nil
                } catch {
                  case e: Exception => Nil
                }
              case _ =>
                Nil
            }
          }
          val l2 = {
            //if not we try t=s....
            checkReplacement( t, s, f, main ) match {
              case EqualModuloEquality( _ ) =>
                val rule = CutRule( leftproof, eq,
                  EqualityLeftRule( WeakeningLeftRule( rightproof, eq ), eq, f, main ), eq )
                try {
                  ContractionMacroRule( rule, fs, strict = false ) :: Nil
                } catch {
                  case e: Exception => Nil
                }
              case _ =>
                Nil
            }
          }
          l1 ++ l2
        } )

        require( inferences.nonEmpty, "Could not infer an eq:l rule from left parent " + f( leftproof.endSequent )
          + " and " + f( rightproof.endSequent ) + " to infer " + f( fs ) )
        if ( inferences.size > 1 )
          debug( "WARNING: Inference to create eq:l rule is not uniquely specified from left parent "
            + leftproof.endSequent + " and " + rightproof.endSequent + " to infer " + fs )

        inferences.head :: stack

      case "EQR" =>
        //we find all candidates, i.e. equations e: s=t in the left parent and pair it with possible formulas f
        // from the right parent together with possible main formulas in the conclusion
        val righteqssucc = rightproof.endSequent.succedent
        val candidates = for (
          e @ Eq( s, t ) <- lefteqs;
          f <- righteqssucc;
          main <- fs.succedent;
          if canReplace( s, t, f, main )
        ) yield { ( s, t, e, f, main ) }

        require( candidates.nonEmpty, "For an eq:r rule, could not find a possible replacement of an equation from "
          + lefteqs.map( f( _ ) ).mkString( "(", ",", ")" ) + " in " +
          fs.succedent.map( f( _ ) ).mkString( "(", ",", ")" ) )

        //now we try to create an inference from each candidate
        val inferences: Seq[LKProof] = candidates.flatMap( args => {
          val ( s, t, eq, f, main ) = args

          val l1 = {
            //print("Trying"+f(s)+"="+f(t)+" in "+f(main))
            //we check if we can paramodulate s=t ...
            checkReplacement( s, t, f, main ) match {
              case EqualModuloEquality( _ ) =>
                //println("found!")
                val rule = CutRule( leftproof, eq,
                  EqualityRightRule( WeakeningLeftRule( rightproof, eq ), eq, f, main ), eq )
                try {
                  ContractionMacroRule( rule, fs, strict = false ) :: Nil
                } catch {
                  case e: Exception => Nil
                }
              case _ =>
                Nil
            }
          }

          val l2 = {
            //if not, we try t=s....
            //print("Trying"+f(t)+"="+f(s)+" in "+f(main))
            checkReplacement( t, s, f, main ) match {
              case EqualModuloEquality( _ ) =>
                //println("found!")
                val rule = CutRule( leftproof, eq,
                  EqualityRightRule( WeakeningLeftRule( rightproof, eq ), eq, f, main ), eq )
                try {
                  ContractionMacroRule( rule, fs, strict = false ) :: Nil
                } catch {
                  case e: Exception => Nil
                }

              case _ =>
                Nil
            }
          }

          l1 ++ l2
        } )

        require( inferences.nonEmpty, "Could not infer an eq:r rule from left parent " + f( leftproof.endSequent )
          + " and " + f( rightproof.endSequent ) + " to infer " + f( fs ) )
        if ( inferences.size > 1 )
          debug( "WARNING: Inference to create eq:r rule is not uniquely specified from left parent "
            + leftproof.endSequent + " and " + rightproof.endSequent + " to infer " + fs )

        inferences.head :: stack

      case _ => throw new Exception( "Expected equational rule but got rule name: " + ruletype )
    }
  }

  //TODO: integrate which definitions were used into the proof
  def handleDefinitions( current_proof: List[LKProof], ruletype: String, fs: HOLSequent, auxterm: Option[LambdaAST],
                         naming: ( String ) => Expr, rt: RToken, llk_definitions: Map[Expr, Expr] ): List[LKProof] = {
    require( current_proof.nonEmpty, "Imbalanced proof tree in application of " + ruletype + " with es: " + fs )
    val parent :: stack = current_proof
    val ( mainsequent, auxsequent, context ) = filterContext( parent.endSequent, fs )
    require(
      auxsequent.formulas.size == 1,
      "Definition rules expect exactly one auxiliary formula, not " + f( auxsequent ) )
    require( ( auxsequent.antecedent.size == mainsequent.antecedent.size ) &&
      ( auxsequent.succedent.size == mainsequent.succedent.size ), "The definition needs to be on the same side!" )

    val definitions = llk_definitions.toList.map( llkd => llkDefinitionToLKDefinition( llkd._1, llkd._2 ) )

    ( auxsequent, mainsequent ) match {
      case ( HOLSequent( Vector(), Vector( aux ) ), HOLSequent( Vector(), Vector( main ) ) ) =>

        //try each definition to infer the main formula
        val rule = definitions.dropWhile( d => try {
          DefinitionRightRule( parent, aux, main );
          false
        } catch { case e: Exception => true } ) match {
          case d :: _ => DefinitionRightRule( parent, aux, main )
          case _ =>
            throw new HybridLatexParserException(
              "Couldn't find a matching definition to infer " + f( main ) + " from " + f( aux ) )
        }
        rule :: stack
      case ( HOLSequent( Vector( aux ), Vector() ), HOLSequent( Vector( main ), Vector() ) ) =>
        //try each definition to infer the main formula
        val rule = definitions.dropWhile( d => try {
          DefinitionLeftRule( parent, aux, main ); false
        } catch { case e: Exception => true } ) match {
          case d :: _ => DefinitionLeftRule( parent, aux, main )
          case _ =>
            throw new HybridLatexParserException(
              "Couldn't find a matching definition to infer " + f( main ) + " from " + f( aux ) )
        }
        rule :: stack
      case _ =>
        throw new HybridLatexParserException(
          "Error in creation of definition rule, can not infer " + f( mainsequent ) + " from " + f( auxsequent ) )
    }
  }

  /*   =================== STRUCTURAL RULES =============================    */
  def handleContraction( current_proof: List[LKProof], ruletype: String,
                         fs: HOLSequent, auxterm: Option[LambdaAST],
                         naming: ( String ) => Expr, rt: RToken ): List[LKProof] = {
    require( current_proof.nonEmpty, "Imbalanced proof tree in application of " + ruletype + " with es: " + fs )
    val parentproof :: stack = current_proof
    val inf = ContractionMacroRule( parentproof, fs, strict = false )
    inf :: stack
  }

  def handleWeakening( current_proof: List[LKProof], ruletype: String,
                       fs: HOLSequent, auxterm: Option[LambdaAST],
                       naming: ( String ) => Expr, rt: RToken ): List[LKProof] = {
    require( current_proof.nonEmpty, "Imbalanced proof tree in application of " + ruletype + " with es: " + fs )
    val parentproof :: stack = current_proof
    //val inf = weaken(parentproof, fs)
    val inf = WeakeningMacroRule( parentproof, fs )
    inf :: stack
  }

  def handleCut( current_proof: List[LKProof], ruletype: String,
                 fs: HOLSequent, auxterm: Option[LambdaAST],
                 naming: ( String ) => Expr, rt: RToken ): List[LKProof] = {
    require( current_proof.size > 1, "Imbalanced proof tree in application of " + ruletype + " with es: " + fs )
    val rightproof :: leftproof :: stack = current_proof

    val auxsequent = ( leftproof.endSequent ++ rightproof.endSequent ) diff fs
    require(
      auxsequent.antecedent.size == 1 && auxsequent.succedent.size == 1,
      "Need exactly one formula in the antecedent and in the succedent of the parents!" + f( auxsequent ) )
    require(
      auxsequent.antecedent.head == auxsequent.succedent.head,
      "Cut formula right (" + auxsequent.antecedent.head +
        ") is not equal to cut formula left (" + auxsequent.succedent.head + ")" )
    val cutformula = auxsequent.antecedent.head
    require(
      leftproof.endSequent.succedent contains cutformula,
      "Cut formula " + cutformula + " must occur in succedent of " + leftproof.endSequent )
    require(
      rightproof.endSequent.antecedent contains cutformula,
      "Cut formula " + cutformula + " must occur in antecedent of " + rightproof.endSequent )
    val inf = CutRule( leftproof, rightproof, cutformula )
    require(
      inf.endSequent multiSetEquals fs,
      "Inferred sequent " + inf.endSequent + " is what was not expected: " + fs )
    inf :: stack
  }

  def handleLink( proofs: Map[Formula, LKProof], current_proof: List[LKProof],
                  ruletype: String, fs: HOLSequent, auxterm: Option[LambdaAST],
                  naming: ( String ) => Expr, rt: RToken ): List[LKProof] = {
    require( auxterm.isDefined, "Can not refer to a subproof(CONTINUEFROM): Need a proof name to link to!" )
    val link = LLKFormulaParser.ASTtoHOL( naming, auxterm.get )
    val ps: List[LKProof] = proofs.toList.flatMap( x => {
      syntacticMatching( x._1, link ) match {
        case None => Nil
        case Some( sub ) =>
          sub( x._2 ) :: Nil
      }
    } )

    require( ps.nonEmpty, "None of the proofs in " +
      proofs.keys.mkString( "(", ",", ")" ) + " matches proof link " + link )
    require(
      ps.head.endSequent.multiSetEquals( fs ),
      "LINK to " + f( link ) + " must give " + f( fs ) + " but gives " + f( ps.head.endSequent ) )

    ps.head :: current_proof

  }

  val axformula = Atom( Const( "AX", To ), Nil )

  def createSubstitution( naming: String => Expr, astlist: List[( ast.Var, LambdaAST )] ): Substitution = {
    val terms: List[( Var, Expr )] = astlist.foldLeft( List[( Var, Expr )]() )( ( list, p ) => {
      (
        LLKFormulaParser.ASTtoHOL( naming, p._1 ).asInstanceOf[Var],
        LLKFormulaParser.ASTtoHOL( naming, p._2 ) ) :: list
    } )
    Substitution( terms.reverse )
  }

  /* =============== Macro Rules ============================ */

  val axioms_prove_sequent = HOLSequent( List( Atom( Const( "AX", To ), Nil ) ), Nil )
  def normalize( exp: Expr ) = betaNormalize( exp )

  def handleEQAxiom( current_proof: List[LKProof], ruletype: String, fs: HOLSequent, auxterm: Option[LambdaAST],
                     subterm: List[( ast.Var, LambdaAST )], naming: ( String ) => Expr,
                     rt: RToken, axioms: Map[Formula, Formula], definitions: Map[Expr, Expr] ): List[LKProof] = {
    require( current_proof.nonEmpty, "Imbalanced proof tree in application of " + ruletype + " with es: " + fs )
    val oldproof :: rest = current_proof
    require( auxterm.isDefined, "Error creating an equational axiom rule: Need instantiation annotation!" )
    val auxf = c( LLKFormulaParser.ASTtoHOLnormalized( naming, auxterm.get ) )

    val sub = createSubstitution( naming, subterm )

    val axs = axioms.toList
    val candidates = axs.flatMap( s => {
      val ( name, ax1 ) = s
      val ( _, ax2 ) = stripUniversalQuantifiers( ax1 )
      val ax = normalize( sub( ax2 ) )
      //println("Trying:"+f(ax)+" against "+f(auxf))
      val r1 = syntacticMatching( ax, auxf ) match {
        case Some( sub ) if sub( ax ) syntaxEquals auxf => ( name, ax1, sub ) :: Nil
        case Some( sub ) =>
          val sub2 = Substitution( sub.map.filter( x => x._1 != x._2 ) )
          if ( sub2( ax ) syntaxEquals auxf )
            ( name, ax1, sub2 ) :: Nil
          else
            Nil
        case None => Nil
      }

      if ( sub( ax ) syntaxEquals auxf ) {
        debug( "User specified sub works!" + f( sub ) )
        ( name, ax1, sub ) :: r1
      } else r1
    } )

    require( candidates.nonEmpty, "Could not find equational axiom for " + f( auxf ) )
    if ( candidates.size > 1 )
      debug( "Warning: Axiom not uniquely specified, possible candidates: " +
        candidates.map( x => f( x._1 ) + " " + x._2 ).mkString( "," ) )
    val ( name, axiom, sub2 ) = candidates.head
    //definitions map (x => if (x._1 syntaxEquals(axformula)) println(x._1 +" -> "+x._2))
    val axiomconjunction = c( definitions( axformula ) )
    val defs = definitions.toList.map( x => llkDefinitionToLKDefinition( x._1, x._2 ) )
    val ( _, axproof ) = getAxiomLookupProof( name, axiom, auxf, axiomconjunction, LogicalAxiom( auxf ), sub2, defs )
    val Some( axdef ) = defs.find( _.what == Const( "AX", To ) )
    val axrule = DefinitionLeftRule( axproof, axiomconjunction, axformula )

    val Eq( s, t ) = auxf

    val auxsequent = oldproof.endSequent diff fs
    val mainsequent = fs diff ( oldproof.endSequent ++ axioms_prove_sequent )
    require( mainsequent.formulas.size == 1, "Exactly one main formula required, not " + f( mainsequent ) )
    require( auxsequent.formulas.size == 1, "Excatly one auxiliary formula needed in parent, not " + f( auxsequent ) )
    val newproof = auxsequent match {
      case HOLSequent( Vector(), Vector( formula ) ) =>
        require(
          mainsequent.antecedent.isEmpty && mainsequent.succedent.size == 1,
          "Auxformula and main formula in eqaxiom rule need to be on the same side of the sequent, not "
            + f( mainsequent ) + " and " + f( auxsequent ) )
        val HOLSequent( Vector(), Vector( main ) ) = mainsequent
        CutRule( axrule, auxf, EqualityRightRule( WeakeningLeftRule( oldproof, auxf ), auxf, formula, main ), auxf )

      case HOLSequent( Vector( formula ), Vector() ) =>
        require(
          mainsequent.antecedent.size == 1 && mainsequent.succedent.isEmpty,
          "Auxformula and main formula in eqaxiom rule need to be on the same side of the sequent, not "
            + f( mainsequent ) + " and " + f( auxsequent ) )
        val HOLSequent( Vector( main ), Vector() ) = mainsequent
        CutRule( axrule, auxf, EqualityLeftRule( WeakeningLeftRule( oldproof, auxf ), auxf, formula, main ), auxf )
    }

    val cproof = ContractionMacroRule( newproof, fs, strict = false )

    cproof :: rest
  }

  def handleInstAxiom( current_proof: List[LKProof], ruletype: String,
                       fs: HOLSequent, auxterm: Option[LambdaAST], subterm: List[( ast.Var, LambdaAST )],
                       naming: ( String ) => Expr, rt: RToken,
                       axioms: Map[Formula, Formula], definitions: Map[Expr, Expr] ): List[LKProof] = {
    require( current_proof.nonEmpty, "Imbalanced proof tree in application of " + ruletype + " with es: " + fs )
    val oldproof :: rest = current_proof
    //require(auxterm.isDefined, "Error creating an stantiate axiom rule: Need instantiation annotation!")
    //val auxf = c(LLKFormulaParser.ASTtoHOL(naming, auxterm.get))
    val auxsequent = oldproof.endSequent diff fs
    val mainsequent = fs diff ( oldproof.endSequent ++ axioms_prove_sequent )

    require(
      mainsequent.formulas.isEmpty,
      "The instantiate axiom rule should not have a main formula, we got: " + f( mainsequent ) )
    require(
      auxsequent.antecedent.size == 1 && auxsequent.succedent.isEmpty,
      "Auxformula formula in inst axiom rule need to be on the lh side of the sequent, not " + f( auxsequent ) )

    val HOLSequent( Vector( auxf_ ), Vector() ) = auxsequent
    val auxf = c( normalize( auxf_ ) )

    //println("auxf="+f(auxf))

    val sub = createSubstitution( naming, subterm )
    //println("sub="+f(sub))
    //println(sub)

    val axs = axioms.toList
    val candidates = axs.flatMap( s => {
      val ( name, ax1 ) = s
      val ( _, ax2 ) = stripUniversalQuantifiers( ax1 )
      val ax = betaNormalize( sub( ax2 ) )
      //println("Trying: "+ f(ax))
      val r1 = syntacticMatching( ax, auxf ) match {
        case Some( sub ) if sub( ax ) syntaxEquals auxf => ( name, ax1, sub ) :: Nil
        case Some( sub2 ) =>
          val sub = Substitution( sub2.map.filterNot( x => x._1 == x._2 ) )
          if ( sub( ax ) syntaxEquals auxf ) {
            ( name, ax1, sub ) :: Nil
          } else {
            info( "wrong sub found!" + f( sub( ax ) ) + " for " + f( auxf ) + " sub=" + f( sub ) + " ax=" + f( ax ) )
            Nil
          };

        //        case Some(sub) => (ax,sub)::Nil
        case None => Nil
      }
      if ( sub( ax ) syntaxEquals auxf ) {
        debug( "User specified sub works!" + f( sub ) )
        ( name, ax1, sub ) :: r1
      } else r1

    } )

    require( candidates.nonEmpty, "Could not find instance axiom for " + f( auxf ) )
    if ( candidates.size > 1 )
      debug( "Warning: Axiom not uniquely specified, possible candidates: " +
        candidates.map( x => f( x._1 ) + " " + x._2 ).mkString( "," ) )
    val ( name, axiom, sub2 ) = candidates.head
    //definitions map (x => if (x._1 syntaxEquals(axformula)) println(x._1 +" -> "+x._2))
    val axiomconjunction = c( definitions( axformula ) )
    val defs = definitions.toList.map( x => llkDefinitionToLKDefinition( x._1, x._2 ) )
    val ( _, axproof ) = getAxiomLookupProof( name, axiom, auxf, axiomconjunction, oldproof, sub2, defs )
    val Some( axdef ) = defs.find( _.what == Const( "AX", To ) )
    val axrule = DefinitionLeftRule( axproof, axiomconjunction, axformula )
    ContractionMacroRule( axrule, fs, strict = false ) :: rest
  }

  /* given a map of elements to lists of dependant elements (e.g. a node's children in a graph),
   calculate a list l where
   * for every element a occurring before an element b in l we know that a does not depend on b.
   * Throws an exception, if the dependency graph contains cycles. */
  def getOrdering[T]( pm: Map[T, List[T]] ): List[T] = {
    val ( leaves, nonleaves ) = pm.partition( el => el._2.isEmpty )
    require( leaves.nonEmpty, "Circular dependency detected: " + pm )
    val leaflist = leaves.keySet.toList
    if ( nonleaves.isEmpty ) {
      leaflist
    } else {
      //remove leaves from the graph
      val rest = nonleaves map ( el => ( el._1, el._2 filterNot ( leaflist contains _ ) ) )
      leaflist ++ getOrdering( rest )
    }
  }

  /* Extracts a map of dependencies between subproofs from a mapping of proof names to the
   token lists representing them. */
  def getDependecyMap( naming: String => Expr, pm: Map[Formula, List[RToken]] ): Map[Formula, List[Formula]] = {
    val proofnames = pm.keySet.toList
    // only keep continuefrom tokens in the lists, map to the formulas in
    // the proofnames against which the dependencies matches
    pm.map( element =>
      ( element._1, element._2.flatMap( _ match {
        case RToken( "CONTINUEFROM", Some( f ), _, _, _ ) =>
          //find the matching proofs
          proofnames.filter( p =>
            syntacticMatching( p, c( LLKFormulaParser.ASTtoHOL( naming, f ) ) ).isDefined ) match {
            //and check if the dependency is ok
            case Nil =>
              throw new HybridLatexParserException( "Could not find a matching dependency for proof " + f
                + " in: " + proofnames.mkString( "," ) )
            case l @ List( d ) =>
              l
            case _ =>
              throw new HybridLatexParserException( "Found more than one matching dependency for proof " + f
                + " in: " + proofnames.mkString( "," ) + " but proof links need to be unique!" )
          }

        case RToken( "INSTLEMMA", Some( f ), _, _, _ ) =>
          //find the matching proofs
          proofnames.filter( p =>
            syntacticMatching( p, c( LLKFormulaParser.ASTtoHOL( naming, f ) ) ).isDefined ) match {
            //and check if the dependency is ok
            case Nil =>
              throw new HybridLatexParserException( "Could not find a matching dependency for proof " + f
                + " in: " + proofnames.mkString( "," ) )
            case l @ List( d ) =>
              l
            case _ =>
              throw new HybridLatexParserException( "Found more than one matching dependency for proof " + f
                + " in: " + proofnames.mkString( "," ) + " but proof links need to be unique!" )
          }

        case RToken( "CONTINUEFROM", _, _, _, _ ) =>
          throw new HybridLatexParserException( "The CONTINUEFROM statement needs a proof as an argument!" )
        case RToken( "INSTLEMMA", _, _, _, _ ) =>
          throw new HybridLatexParserException( "The INSTLEMMA statement needs a proof as an argument!" )
        case _ => Nil
      } ) ) )
  }

  /* remove common context from sequent (fs_old) and inferred sequent (fs_new).
   * return a triple: (sequent with main formula,
   *                   sequent with auxiliary and uncontracted formulas,
   *                   context sequent) */
  def filterContext( fs_old: HOLSequent, fs_new: HOLSequent ): ( HOLSequent, HOLSequent, HOLSequent ) = {
    val ndiff = fs_new diff fs_old
    val odiff = fs_old diff fs_new

    val csequent = fs_new diff ndiff

    try {
      require( ndiff.formulas.length == 1, "We want exactly one primary formula, not: " + f( ndiff ) +
        " in " + f( fs_new ) )
      require( odiff.formulas.nonEmpty, "We want at least one auxiliary formula, not: " + f( odiff ) +
        " in " + f( fs_old ) )
    } catch {
      case e: Exception => throw new HybridLatexParserException( e.getMessage, e )
    }
    ( ndiff, odiff, csequent )
  }

  /* creates a map from axiom names to the corresponding fsequents from a list of axiom tokens,
   * supposed to be passed on to EQAXIOM and INSTAXIOM rules */
  def createAxioms( naming: String => Expr, l: List[AToken] ): Map[Formula, Formula] = {
    l.filter( _.rule == "AXIOMDEC" ).foldLeft( Map[Formula, Formula]() )( ( map, token ) => {
      val AToken( rulename, aname, antecedent, succedent ) = token
      require( aname.nonEmpty, "Axiom declaration " + token + " needs a name!" )
      val aformula: Formula = c( LLKFormulaParser.ASTtoHOL( naming, aname.get ) )
      val ant = antecedent.map( x => c( LLKFormulaParser.ASTtoHOL( naming, x ) ) )
      val suc = succedent.map( x => c( LLKFormulaParser.ASTtoHOL( naming, x ) ) )
      val fs = HOLSequent( ant, suc )
      require( ant.isEmpty && suc.size == 1, "Axiom declarations need to be one positive formula, not " + fs )
      map + ( ( aformula, fs.succedent.head ) )
    } )
  }

  /* creates a binary conjunction tree from a list of formulas */
  def createConjunctions( l: List[Formula] ): Formula = createConjunctions_( l ) match {
    case List( conj )   => conj
    case l @ ( _ :: _ ) => createConjunctions( l )
    case Nil            => throw new HybridLatexParserException( "Could not create conjunction of empty list!" )
  }
  /* for a list of formulas of length n return a list of formulas And(i_1.i_2), etc of size n/2 */
  def createConjunctions_( l: List[Formula] ): List[Formula] = l match {
    case x :: y :: rest => And( x, y ) :: createConjunctions_( rest )
    case _              => l
  }

  /* Checks if what is contained as formula inside a nesting of neg, and, or, imp. Used for a lookup in an
    axiom conjunction */
  private def formula_contains_atom( f: Formula, what: Formula ): Boolean = f match {
    case Neg( x )    => formula_contains_atom( x, what )
    case And( x, y ) => formula_contains_atom( x, what ) || formula_contains_atom( y, what )
    case Imp( x, y ) => formula_contains_atom( x, what ) || formula_contains_atom( y, what )
    case Or( x, y )  => formula_contains_atom( x, what ) || formula_contains_atom( y, what )
    case _           => f == what
  }

  def llkDefinitionToLKDefinition( exp: Expr, to: Expr ) = exp match {
    case Apps( c @ Const( _, _, _ ), args ) if args.forall( { case Var( _, _ ) => true; case _ => false } ) =>
      val vs = args.map( { case v @ Var( _, _ ) => v } )
      Definition( c, Abs.Block( vs, to ) )
    case _ =>
      throw new Exception( s"Can not convert LLK Definition $exp -> $to to LK Definition!" )
  }

  /* Creates the definition map from a list of ATokens. Also adds a defintion for all the axioms. */
  def createDefinitions( naming: String => Expr, l: List[AToken], axioms: Map[Formula, Formula] ): Map[Expr, Expr] = {
    val preddefs = l.filter( _.rule == "PREDDEF" ).foldLeft( Map[Expr, Expr]() )( ( map, token ) => {
      val ( left, right ) = token match {
        case AToken( _, _, List( left ), List( right ) ) => ( left, right )
        case _ => throw new HybridLatexParserException(
          "Only one formula allowed as parameters in predicate definition declaration, got " + token )
      }

      val lformula = c( LLKFormulaParser.ASTtoHOL( naming, left ) )
      val rformula = c( LLKFormulaParser.ASTtoHOL( naming, right ) )

      lformula match {
        case Atom( _, _ ) =>
          require(
            freeVariables( lformula ) == freeVariables( rformula ),
            "Definition formulas " + lformula + " and " + rformula + " do not have the same set of free variables!" +
              sys.props( "line.separator" ) + freeVariables( lformula ) + sys.props( "line.separator" ) +
              freeVariables( rformula ) )
          map + ( ( lformula, rformula ) )
        case _ => throw new HybridLatexParserException( "Left hand side of a definition must be an atom, but is " +
          lformula )
      }

    } )

    val fundefs = l.filter( _.rule == "FUNDEF" ).foldLeft( preddefs )( ( map, token ) => {
      val ( left, right ) = token match {
        case AToken( _, _, List( left ), List( right ) ) => ( left, right )
        case _ => throw new HybridLatexParserException(
          "Only one formula allowed as parameters in function definition declaration, got " + token )
      }

      val lexpression = LLKFormulaParser.ASTtoHOL( naming, left )
      val rexpression = LLKFormulaParser.ASTtoHOL( naming, right )

      ( lexpression, rexpression ) match {
        case ( f1 @ HOLFunction( _, _ ), f2 @ HOLFunction( _, _ ) ) =>
          require(
            f1.ty == f2.ty,
            "The types of defined formulas and definition must match, but are: " + f1.ty + " and " + f2.ty )
          require(
            freeVariables( lexpression ) == freeVariables( rexpression ),
            "Definition function " + lexpression + " and " + rexpression +
              " do not have the same set of free variables!" )
          map + ( ( lexpression, rexpression ) )
        case _ => throw new HybridLatexParserException(
          "Left hand side of a definition must be an atom, but is " + lexpression )
      }

    } )

    //TODO: check name clashes
    val defs_withaxioms = axioms.foldLeft( fundefs )( ( map, pair ) => map + pair )

    if ( axioms.nonEmpty ) {
      val axiomformula = createConjunctions( axioms.keys.toList )
      defs_withaxioms + ( ( axformula, axiomformula ) )
    } else
      defs_withaxioms

  }

  /* remove common context from 2 sequents (fs_old1, fs_old2) and inferred sequent (fs_new).
   * return a triple: (sequent with main formula,
   *                   sequent with auxiliary and uncontracted formulas,
   *                   context sequent) */
  def filterContext( fs_old1: HOLSequent, fs_old2: HOLSequent,
                     fs_new: HOLSequent ): ( HOLSequent, HOLSequent, HOLSequent ) =
    filterContext( fs_old1 ++ fs_old2, fs_new )

  /* removes univarsal quantifiers from f and returns the list of quantified variables together
   * with the stripped formula */
  def stripUniversalQuantifiers( f: Formula ): ( List[Var], Formula ) = stripUniversalQuantifiers( f, Nil )
  @tailrec
  private def stripUniversalQuantifiers( f: Formula, acc: List[Var] ): ( List[Var], Formula ) = f match {
    case All( x, f_ ) => stripUniversalQuantifiers( f_, x.asInstanceOf[Var] :: acc )
    case _            => ( acc.reverse, f )
  }

  /* Checked cast of Expr to Formula which gives a nicer error message */
  private def c( e: Expr ): Formula =
    e match {
      case formula: Formula => formula
      case _                => throw new Exception( "Could not convert " + e + " to a HOL Formula!" )
    }

  def getAxiomLookupProof( name: Formula, axiom: Formula, instance: Formula,
                           axiomconj: Formula, axiomproof: LKProof,
                           sub: Substitution, definitions: List[Definition] ): ( Formula, LKProof ) = {
    axiomconj match {
      case Atom( c @ Const( n, To, _ ), List() ) =>
        val pi = proveInstanceFrom( axiom, instance, sub, axiomproof )
        val d = definitions.find( _.what == c ).getOrElse(
          throw new Exception(
            s"could not find a definition for $c in ${definitions.map( _.what ).sortBy( _.name )}" ) )
        ( axiomconj, DefinitionLeftRule( pi, axiom, axiomconj ) )

      case And( x, y ) if formula_contains_atom( x, name ) =>
        val ( aux, uproof ) = getAxiomLookupProof( name, axiom, instance, x, axiomproof, sub, definitions )
        ( axiomconj, AndLeftRule( WeakeningLeftRule( uproof, y ), aux, y ) )

      case And( x, y ) if formula_contains_atom( y, name ) =>
        val ( aux, uproof ) = getAxiomLookupProof( name, axiom, instance, y, axiomproof, sub, definitions )
        ( axiomconj, AndLeftRule( WeakeningLeftRule( uproof, x ), x, aux ) )

      case _ =>
        throw new Exception( "Could not create a proof for inference AX :- " +
          instance + sys.props( "line.separator" ) + " " + name + " does not occur in " + axiomconj )
    }
  }

  //TODO:move this code to an appropriate place
  def proveInstance( axiom: Formula, instance: Formula, sub: Substitution ): LKProof = {
    //val (qs,body) = stripUniversalQuantifiers(axiom)
    proveInstance_( axiom, instance, sub, LogicalAxiom( instance ) )._2
  }

  def proveInstanceFrom( axiom: Formula, instance: Formula, sub: Substitution, uproof: LKProof ): LKProof = {
    //val (qs,body) = stripUniversalQuantifiers(axiom)
    proveInstance_( axiom, instance, sub, uproof )._2
  }
  def proveInstance_( axiom: Formula, instance: Formula,
                      sub: Substitution, axiomproof: LKProof ): ( Formula, LKProof ) = {
    //    println("Prove instance with sub "+f(sub))
    axiom match {
      case All( v, s ) =>
        val ( aux, uproof ) = proveInstance_( s, instance, sub, axiomproof )
        ( c( sub( axiom ) ), ForallLeftRule( uproof, c( sub( axiom ) ), sub.map( v ) ) )
      case f if normalize( sub( f ) ) syntaxEquals instance =>
        ( instance, axiomproof )
      case _ => throw new Exception(
        "Implementation error! Could not de++ " + f( axiom ) + " subterm=" + sub( axiom ) + " need=" + f( instance ) )
    }
  }
}
