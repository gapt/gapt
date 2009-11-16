/**
 * Description: Parses the CERES XML format version 5.0
 * 
 * TODO: Support for 
 *  prooftool-related elements (variabledefinitions, ...)
 *  substitution element
 *  formulavariable element
 * 
 * All parsers expect the XML to conform to the DTD, no checking is done!
 */

package at.logic.parsing.language.xml

import scala.xml._
import scala.xml.Utility.trim
import at.logic.language.lambda.TypedLambdaCalculus._
import at.logic.parsing.ParsingException
import at.logic.parsing.readers.XMLReaders.NodeReader
import at.logic.language.hol.HigherOrderLogic._
import at.logic.language.lambda.Symbols._
import at.logic.language.lambda.Types._
import at.logic.language.hol.LogicSymbols.{ConstantStringSymbol, VariableStringSymbol}
import at.logic.calculi.lk.LK._
import scala.collection.mutable.ArrayBuffer

object XMLParser {

  trait XMLNodeParser {
    def getInput() : scala.xml.Node
  }

  object XMLUtils {
    def nodesToAbstractTerms(ns : List[Node]) : List[HOLTerm] =
      ns.map( c => (new NodeReader( c ) with XMLAbstractTermParser).getAbstractTerm() )
    
    def nodesToFormulas(ns : List[Node]) : List[HOLFormula] =
      ns.map( c => (new NodeReader( c ) with XMLFormulaParser).getFormula() )

    def permStringToFun( perm: String, size: Int ) : Int => Int =
    {
      val cycles = permStringToCycles( perm, size )
      def fun( i : Int ) = cycles.apply( i )
      fun
    }

    // ported from C++ constructor of Permutation
    def permStringToCycles( perm: String, size: Int ) : Array[Int] =
    {
      var end_cyc = 0
      var start_cyc = perm.indexOf( "(", end_cyc )
      var cycles : List[Array[Int]] = Nil
      while ( start_cyc != -1 )
      {
        end_cyc = perm.indexOf( ")", start_cyc + "(".length )
        val cyc = perm.substring( start_cyc + "(".length, end_cyc )
        cycles = cycles ::: List(cycleStringToArray( cyc ))
        start_cyc = perm.indexOf( "(", end_cyc + ")".length )
      }
      cyclesToVector( cycles, size )
    }

    // ported from C++ constructor of MVector
    /*
    def cycleStringToArray( cyc: String ) =
    {
      var start_num = 0
      var dpos = 0
      val arr = new ArrayBuffer[Int]
      while ( start_num < cyc.length )
      {
        dpos = cyc.indexOf( " ", start_num )
        if ( dpos == -1 )
          dpos = cyc.length
        var num = cyc.substring( start_num, dpos )
        arr += num.toInt - 1
        start_num = dpos + " ".length
      }
      arr.toArray
    }
    */

    // More Scala-y implementation
    def cycleStringToArray( cyc: String ) = cyc.split(' ').map( s => s.toInt - 1 )

    // creates a permutation vector out of a list of cycles
    def cyclesToVector( cycles: List[Array[Int]], size: Int ) =
    {
      val vec = new Array[Int]( size )

      // init with identity
      for ( i <- 0 until vec.length )
        vec.update( i, i )

      cycles.foreach( cyc => {
        for ( i <- 0 until cyc.length - 1 )
          vec.update( cyc.apply( i ), cyc.apply( i + 1 ) )
        vec.update( cyc.apply( cyc.length - 1 ), cyc.apply( 0 ) )
      } )
      vec
    }
  }

  def idPerm(x: Int) = x

  trait XMLSequentParser extends XMLNodeParser {
    def getSequent() : Sequent[HOL] = getSequent( getInput() )
    def getSequentList() : List[Sequent[HOL]] = getSequentList( getInput() )
    def getFormulaList() : List[HOLFormula] = getFormulaList( getInput() )
    
    def getSequent(n: Node) : Sequent[HOL] =
      trim(n) match {
        case <sequent>{ns @ _*}</sequent> =>
          Sequent(getFormulaList(ns.first), getFormulaList(ns.last))
        case _ => throw new ParsingException("Could not parse XML: " + n.toString)
      }
    
    def getSequentList(n: Node) =
      trim(n) match {
        case <sequentlist>{ns @ _*}</sequentlist> => {
          ns.map( n => getSequent(n) ).toList
        }
        case _ => throw new ParsingException("Could not parse XML: " + n.toString)
      }
    
    def getFormulaList(n: Node) =
      trim(n) match {
        case <formulalist>{ns @ _*}</formulalist> => {
          ns.map( n => (new NodeReader(n) with XMLFormulaParser).getFormula() ).toList
        }
        case _ => throw new ParsingException("Could not parse XML: " + n.toString)
      }
  }

  trait XMLProofParser extends XMLNodeParser {
    def getProof() : LKProof[HOL] = getProof( getInput() )
    
    def getProof( n : Node ) : LKProof[HOL] = getProof( n, idPerm, idPerm )._1

    // perm stores the permutation of the end-sequent, i.e. given a
    // position in the sequent in the XML format, it returns a position
    // in the corresponding sequent in our rules in gapt format
    def getProof(n : Node, l_perm : Int => Int, r_perm : Int => Int ) : (LKProof[HOL], Int => Int, Int => Int) =
      trim(n) match {
        case <proof>{ ns @ _* }</proof> => {
          // TODO: read symbol, calculus
          getProof( ns.first, l_perm, r_perm )
        }
        case <rule>{ ns @ _* }</rule> => {
          val rt = n.attribute("type").get.first.text
          val param = if ( n.attribute("param") == None ) None else Some( n.attribute("param").get.first.text )
          val conc = ( new NodeReader(ns.first) with XMLSequentParser ).getSequent()
          // TODO: according to DTD, last two items may be substitution
          // or lambdasubstitution! we _wrongly_ assume for the moment
          // that all further children are rules/prooflinks
          val recl = ns.toList.tail.map( n => getProof( n, l_perm, r_perm ) )
          val prems = recl.map( p => p._1 )
          val l_perms = recl.map( p => p._2 )
          val r_perms = recl.map( p => p._3 )
          createRule( rt, conc, prems, l_perms, r_perms, param )
        }
        //case <prooflink/> => {
          //n.attribute("symbol").get.first.text
          // TODO: create DAG Proof!?
        //  None
        //}
        case _ => throw new ParsingException("Could not parse XML: " + n.toString)
      }

    def createRule( rt : String, conc: Sequent[HOL], prems: List[LKProof[HOL]],
      l_perms: List[Int => Int], r_perms : List[Int => Int], param : Option[String] ) : (LKProof[HOL], Int => Int, Int => Int) =
      rt match {
        case "axiom" => ( Axiom(conc), idPerm, idPerm )
        case "permr" => {
          if ( param == None )
            throw new ParsingException("Rule type is permr, but param attribute is not present.")
          val param_s = param.get
          val prem = prems.first
          val l_perm = l_perms.first
          def r_perm(i : Int) = XMLUtils.permStringToFun( param_s, prem.root.succedent.size )( r_perms.first(i) )
          ( prem, l_perm, r_perm )
        }
        case "perml" => {
          if ( param == None )
            throw new ParsingException("Rule type is perml, but param attribute is not present.")
          val param_s = param.get
          val prem = prems.first
          val r_perm = r_perms.first
          def l_perm(i : Int) = XMLUtils.permStringToFun( param_s, prem.root.antecedent.size )( l_perms.first(i) )
          ( prem, l_perm, r_perm )
        }
        case "andr" => {
          val l_prem = prems.first
          val r_prem = prems.last
          def l_perm_l = l_perms.first
          def l_perm_r = r_perms.first
          def r_perm_l = l_perms.last
          def r_perm_r = r_perms.last
          val l_p_s = l_prem.root.succedent.size
          val l_p_a = l_prem.root.antecedent.size
          val r_p_s = r_prem.root.succedent.size 
          val r_p_a = r_prem.root.antecedent.size
          def new_perm_l(i : Int) =
            if ( i < l_p_a )
              l_perm_l( i )
            else
              r_perm_l( i - l_p_a ) + l_p_a
          def new_perm_r(i : Int) =
            if ( i == l_p_s + r_p_s - 2 ) // main formula
              0
            else if ( i < l_p_s - 1 )
              l_perm_r( i ) + 1
            else
              r_perm_r( i - l_p_s ) + l_p_s + 1
          val auxf_l = l_prem.root.succedent.apply( l_perm_r( l_prem.root.succedent.size - 1 ) )
          val auxf_r = r_prem.root.succedent.apply( r_perm_r( r_prem.root.succedent.size - 1 ) )
          ( AndRightRule( l_prem, r_prem, auxf_l, auxf_r ),
            new_perm_l, new_perm_r )
        }
        case "orr1" => {
          val prem = prems.first
          val l_perm = l_perms.first
          def r_perm(i : Int) =
            if ( i == prem.root.succedent.size - 1 ) // main formula
              0
            else
              r_perms.first(i)
          val auxf = prem.root.succedent.apply( r_perms.first( prem.root.succedent.size - 1 ) )
          val mainf = conc.succedent.apply( conc.succedent.size - 1 )
          mainf match {
            // FIXME: this typecast sucks!
            case Or(_, weakf : HOLFormula) => ( OrRight1Rule( prem, auxf, weakf ), l_perm, r_perm )
            case _ => throw new ParsingException("Rule type is orr1, but main formula is not a disjunction.")
          }
        }
        case _ => throw new ParsingException("Unknown rule type: " + rt)
      }
  }
  /*
  trait XMLDefinitionParser extends XMLNodeParser {
    def getDefinition() = getDefinition( getInput() )
    
    def getDefinition(n : Node) =
      n match {
        case <definitionlist>{_*}</definitionlist> =>
        case <formuladef>{_*}</formuladef> =>
        case <termdef>{_*}</termdef> =>
        case <indirecttermdef>{_*}</indirecttermdef> =>
      }
  }
  */
  
/*
This class parses the elements subsumed under the entity &formula;
 */
  trait XMLFormulaParser extends XMLNodeParser {
    def getFormula() : HOLFormula = getFormula( getInput() )

    def getFormula(n : Node) : LambdaExpression[HOL] with Formula[HOL] =
      trim(n) match {
        case <constantatomformula>{ ns @ _* }</constantatomformula>
          => Atom(new ConstantStringSymbol( n.attribute("symbol").get.first.text ),
                  XMLUtils.nodesToAbstractTerms(ns.toList))
        // FIXME: this cast is necessary because of the formula trait?
        // ask tomer!
        case <variableatomformula>{ ns @ _* }</variableatomformula>
          => AppN( (new NodeReader( ns.first ) with XMLSetTermParser).getSetTerm(),
                   XMLUtils.nodesToAbstractTerms( ns.toList.tail ) ).asInstanceOf[HOLFormula]
        case <definedsetformula>{ ns @ _* }</definedsetformula>
          => AppN( (new NodeReader( ns.first ) with XMLSetTermParser).getSetTerm(),
                   XMLUtils.nodesToAbstractTerms( ns.toList.tail ) ).asInstanceOf[LambdaExpression[HOL] with Formula[HOL]]
        case <conjunctiveformula>{ ns @ _* }</conjunctiveformula> 
          => createConjunctiveFormula(n.attribute("type").get.first.text,
                                         XMLUtils.nodesToFormulas(ns.toList))
        case <quantifiedformula>{ ns @ _* }</quantifiedformula> =>
        {
                  val variable = ( new NodeReader(ns.first) with XMLTermParser).getTerm().asInstanceOf[Var[HOL]]
                  val form = ( new NodeReader(ns.last) with XMLFormulaParser).getFormula() 
                  createQuantifiedFormula( n.attribute("type").get.first.text,
                                           variable, form )
        }
        case <secondorderquantifiedformula>{ ns @ _*}</secondorderquantifiedformula> =>
        {
          val variable = ( new NodeReader(ns.first) with XMLSetTermParser).getSetTerm().asInstanceOf[Var[HOL]]
          val form = ( new NodeReader(ns.last) with XMLFormulaParser).getFormula()
          createQuantifiedFormula( n.attribute("type").get.first.text,
                                              variable, form )

        }
        case _ => throw new ParsingException("Could not parse XML: " + n.toString)
      }

    def createConjunctiveFormula(sym: String, formulas: List[LambdaExpression[HOL] with Formula[HOL]]) : LambdaExpression[HOL] with Formula[HOL] =
    {
      sym match {
        case "and" => And(formulas.first, formulas.last)
        case "or" => Or(formulas.first, formulas.last)
        case "impl" => Imp(formulas.first, formulas.last)
        case "neg" => Neg(formulas.first)
        case _ => throw new ParsingException("Could not parse conjunctiveformula type: " + sym)
      }
    }

    def createQuantifiedFormula(sym: String, variable: Var[HOL], formula: LambdaExpression[HOL] with Formula[HOL]) : LambdaExpression[HOL] with Formula[HOL] =
      sym match {
        case "all" => AllVar(variable, formula)
        case "exists" => ExVar(variable, formula)
        case _ => throw new ParsingException("Could not parse quantifiedformula type: " + sym)
      }
  }
  
/*
This class parses the elements subsumed under the entity &abstractterm;
 */
  trait XMLAbstractTermParser extends XMLNodeParser {
    def getAbstractTerm() : HOLTerm = getAbstractTerm( getInput() )
    
    def getAbstractTerm(n: Node) : HOLTerm =
      try {
        (new NodeReader(n) with XMLTermParser).getTerm()
      }
      catch {
        case e : ParsingException =>
          {
            (new NodeReader(n) with XMLSetTermParser).getSetTerm()
          }
      }
  }

/*
This class parses the elements subsumed under the entity &term;
 */
  trait XMLTermParser extends XMLNodeParser {
    def getTerm() : HOLTerm = getTerm(getInput())
    
    def getTerm(n: Node) : HOLTerm =
      trim(n) match {
        case <variable/> => Var[HOL](new VariableStringSymbol( n.attribute("symbol").get.first.text ), Ti())
        case <constant/> => Var[HOL](new ConstantStringSymbol( n.attribute("symbol").get.first.text ), Ti())
        case <function>{ ns @ _* }</function> => createFunction(n.attribute("symbol").get.first.text,
                                                             XMLUtils.nodesToAbstractTerms(ns.toList))
        case _ => throw new ParsingException("Could not parse XML: " + n.toString)
      }
    def createFunction( sym: String, args : List[HOLTerm] ) : HOLTerm =
      AppN( Var[HOL](new ConstantStringSymbol(sym), FunctionType( Ti(), args.map( a => a.exptype ) ) ),
            args)
  }

/*
This class parses the elements subsumed under the entity &setterm;
 */
  trait XMLSetTermParser extends XMLNodeParser {
    def getSetTerm() : HOLTerm = getSetTerm(getInput())
    
    def getSetTerm(n: Node) : HOLTerm =
      trim(n) match {
        // FIXME: the arity of the second-order variable is not
        // provided here, so we assume for the moment that all second order
        // variables have type i -> o.
        case <secondordervariable/> => 
          Var[HOL](new VariableStringSymbol( n.attribute("symbol").get.first.text ),
                   i -> o)
        case <lambdasubstitution>{ ns @ _* }</lambdasubstitution> => {
          AbsN( (new NodeReader(ns.first) with XMLVariableListParser).getVariableList(),
                (new NodeReader(ns.last) with XMLFormulaParser).getFormula() )
        }
        // TODO: treat definitional aspect of definedset
        case <definedset>{ ns @ _* }</definedset> =>
        {
          val args = XMLUtils.nodesToAbstractTerms( ns.toList )
          AppN( Var[HOL](new ConstantStringSymbol( n.attribute("symbol").get.first.text ),
                         FunctionType( i -> o, args.map( t => t.exptype ) ) ),
                args )
        }
        case _ => throw new ParsingException("Could not parse XML: " + n.toString)
      }
  }
  
  trait XMLVariableListParser extends XMLNodeParser {
    def getVariableList() : List[Var[HOL]] = getVariableList(getInput())
    
    def getVariableList(n: Node) : List[Var[HOL]] =
      trim(n) match {
        case <variablelist>{ns @ _*}</variablelist> => {
          ns.map( n => (new NodeReader(n) with XMLTermParser).getTerm().asInstanceOf[Var[HOL]] ).toList
        }
        case _ => throw new ParsingException("Could not parse XML: " + n.toString)
      }
  }
}
