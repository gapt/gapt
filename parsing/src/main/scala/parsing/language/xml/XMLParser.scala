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
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.parsing.ParsingException
import at.logic.parsing.readers.XMLReaders.NodeReader
import at.logic.language.hol.propositions._
import at.logic.language.hol.quantifiers._
import at.logic.language.hol.propositions.TypeSynonyms._
import at.logic.language.hol.propositions.ImplicitConverters._
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lk.definitionRules._
import at.logic.calculi.lk.equationalRules._
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.calculi.lk.base._

/**
 * This object contains several classes responsible for the parsing of the CERES XML
 * format, according to the proofdatabase.dtd version 5.0.
 */
object XMLParser {

  /** 
   * All concrete parsers for CERES XML elements will implement this trait
   */
  trait XMLNodeParser {
    def getInput() : scala.xml.Node
  }

  /**
   * This object provides some utility functions which are useful when parsing
   * CERES XML elements.
   */
  object XMLUtils {
    /**
     * This function converts a list of nodes, which are assumed to be instances
     * of the XML &amp;abstractterm; entity, to a list of HOLTerms.
     *
     * @param ns A list of nodes, each of which is an instance of the XML 
                 &amp;abstractterm; entity.
     * @return   A list of HOLTerms corresponding to the list of nodes.
     * @see XMLParser.XMLAbstractTermParser
     */
    def nodesToAbstractTerms(ns : List[Node]) : List[HOLTerm] =
      ns.map( c => (new NodeReader( c ) with XMLAbstractTermParser).getAbstractTerm() )
   
    /**
     * This function converts a list of nodes, which are assumed to be instances
     * of the XML &amp;formula; entity, to a list of HOLFormulas.
     *
     * @param ns A list of nodes, each of which is an isntance of the XML
     *           &amp;formula; entity.
     * @return   A list of HOLFormulas corresponding to the list of nodes.
     * @see XMLParser.XMLFormulaParser
     */
    def nodesToFormulas(ns : List[Node]) : List[HOLFormula] =
      ns.map( c => (new NodeReader( c ) with XMLFormulaParser).getFormula() )


    /**
     * This function takes a permutation string (encoded as a list of cycles,
     * see http://www.logic.at/ceres/downloads/calculus_LK.pdf) and the size of
     * the permutation, and returns the permutation as a function from Int to Int.
     * The size of the permutation has to be supplied, as the string format allows
     * leaving out trivial cycles.
     *
     * @param perm The permutation in string format.
     * @param size The size of the permutation.
     * @return     The permutation as a function.
     */
    def permStringToFun( perm: String, size: Int ) : Int => Int =
    {
      val cycles = permStringToCycles( perm, size )
      def fun( i : Int ) = cycles.apply( i )
      fun
    }

    // Ported from C++ CERES method Permutation::getInverse()
    def invertCycles( cycles: Array[Int] ) : Array[Int] =
    {
      val inv = new Array[Int]( cycles.length )
      for ( i <- 0 until cycles.length )
        inv.update( cycles.apply( i ), i )
      inv
    }

    /**
     * This function takes a permutation string (encoded as a list of cycles,
     * see http://www.logic.at/ceres/downloads/calculus_LK.pdf) and the size of
     * the permutation, and returns the permutation as an Array of Ints.
     * The size of the permutation has to be supplied, as the string format allows
     * leaving out trivial cycles.
     *
     * This function was ported from the constructor of the Permutation class in
     * C++ CERES.
     *
     * @param perm The permutation in string format.
     * @param size The size of the permutation.
     * @return     The permutation as an Array of Ints.
     */
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
      // We have to invert the cycles for our purposes!
      // i.e. read the permutation bottom up instead of top down
      invertCycles( cyclesToVector( cycles, size ) )
    }

    /**
     * This function takes a cycle string (a whitespace separated list of integers,
     * see http://www.logic.at/ceres/downloads/calculus_LK.pdf) 
     * and returns the cycle as an Array of Ints. For example, the string "2 7 3"
     * will become the vector [2, 7, 3].
     *
     * This function is based on the constructor of the MVector class in
     * C++ CERES.
     *
     * @param perm The permutation in string format.
     * @param size The size of the permutation.
     * @return     The permutation as an Array of Ints.
     */
    def cycleStringToArray( cyc: String ) = cyc.split(' ').map( s => s.toInt - 1 )

    /**
     * This function takes a permutation (encoded as a list of cycles,
     * see http://www.logic.at/ceres/downloads/calculus_LK.pdf) and the size of
     * the permutation, and returns the permutation as an Array of Ints.
     * The size of the permutation has to be supplied, as the format allows
     * leaving out trivial cycles.
     *
     * This function was ported from the Permutation::cycles2Vector method in
     * C++ CERES.
     *
     * @param perm The permutation in string format.
     * @param size The size of the permutation.
     * @return     The permutation as an Array of Ints.
     */
    def cyclesToVector( cycles: List[Array[Int]], size: Int ) =
    {
      val vec = new Array[Int]( size )

      // init with identity to account for trivial cycles
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

  /**
   * This trait parses XML elements &lt;sequent&gt;, &lt;sequentlist&gt; and &lt;formulalist&gt;
   * into the respective objects.
   */
  trait XMLSequentParser extends XMLNodeParser {
    /**
     * If the Node provided by XMLNodeParser is a &lt;sequent&gt; element,
     * a Sequent object corresponding to the Node is returned.
     *
     * @return A Sequent object corresponding to the Node provided by getInput().
     * @throws ParsingException If the Node provided by getInput() is not a &lt;sequent&gt; Node.
     */
    def getSequent() : Sequent = getSequent( getInput() )

    /**
     * If the Node provided by XMLNodeParser is a &lt;sequentlist&gt; element,
     * a List of Sequent objects corresponding to the Node is returned.
     *
     * @return A List of Sequent objects corresponding to the Node provided by getInput().
     * @throws ParsingException If the Node provided by getInput() is not a &lt;sequentlist&gt; Node.
     */
    def getSequentList() : List[Sequent] = getSequentList( getInput() )

    /**
     * If the Node provided by XMLNodeParser is a &lt;formulalist&gt; element,
     * a List of HOLFormula objects corresponding to the Node is returned.
     *
     * @return A List of HOLFormula objects corresponding to the Node provided by getInput().
     * @throws ParsingException If the Node provided by getInput() is not a &lt;formulalist&gt; Node.
     */
    def getFormulaList() : List[HOLFormula] = getFormulaList( getInput() )

     /**
     * If the Node n is a &lt;sequent&gt; element,
     * a Sequent object corresponding to the Node is returned.
     *
     * @return A Sequent object corresponding to n.
     * @throws ParsingException If n is not a &lt;sequent&gt; node.
     */   
    def getSequent(n: Node) : Sequent =
      trim(n) match {
        case <sequent>{ns @ _*}</sequent> =>
          Sequent(getFormulaList(ns.first), getFormulaList(ns.last))
        case _ => throw new ParsingException("Could not parse XML: " + n.toString)
      }
 
     /**
     * If the Node n is a &lt;sequentlist&gt; element,
     * a List of Sequent objects corresponding to the Node is returned.
     *
     * @return A List of Sequent objects corresponding to n.
     * @throws ParsingException If n is not a &lt;sequentlist&gt; node.
     */
    def getSequentList(n: Node) =
      trim(n) match {
        case <sequentlist>{ns @ _*}</sequentlist> => {
          ns.map( n => getSequent(n) ).toList
        }
        case _ => throw new ParsingException("Could not parse XML: " + n.toString)
      }

     /**
     * If the Node n is a &lt;formulalist&gt; element,
     * a List of HOLFormula objects corresponding to the Node is returned.
     *
     * @return A List of HOLFormula objects corresponding to n.
     * @throws ParsingException If n is not a &lt;formulalist&gt; node.
     */   
    def getFormulaList(n: Node) =
      trim(n) match {
        case <formulalist>{ns @ _*}</formulalist> => {
          ns.map( n => (new NodeReader(n) with XMLFormulaParser).getFormula() ).toList
        }
        case _ => throw new ParsingException("Could not parse XML: " + n.toString)
      }
  }

  trait XMLProofDatabaseParser extends XMLNodeParser {
    def getProofs() : List[LKProof] = getProofs( getInput() )
    def getProofs( pdb : Node ) : List[LKProof] =
      (pdb\"proof").map( n => ( new NodeReader( n ) with XMLProofParser ).getProof() ).toList
  }

  /**
   * This trait parses XML elements &lt;proof&gt;, &lt;rule&gt; and &lt;prooflink&gt;
   * into the respective objects.
   *
   * TODO: prooflink parsing is not supported yet! 
   */
  trait XMLProofParser extends XMLNodeParser {
    /**
     * If the Node provided by XMLNodeParser is a &lt;proof&gt;, &lt;rule&gt; or
     * &lt;prooflink&gt; element,
     * an LKProof object corresponding to the Node is returned. Note that the
     * LK proofs in gapt differ from the LK proofs in the XML format: the XML format
     * sees sequents in proofs as pairs of lists of formulas, while gapt sees sequents
     * in proofs as pairs of sets of formula occurrences. The parser converts the
     * XML proofs in such a way that the ancestor relation is preserved.
     *
     * TODO: prooflink parsing is not supported yet!
     *
     * @return An LKProof object corresponding to the Node provided by getInput().
     * @throws ParsingException If the Node provided by getInput() is not a &lt;proof&gt;,
     * &lt;rule&gt; or &lt;prooflink&gt; Node.
     */
    def getProof() : LKProof = getProof( getInput() )
    /**
     * If n is a &lt;proof&gt;, &lt;rule&gt; or &lt;prooflink&gt; Node,
     * an LKProof object corresponding to the Node is returned. Note that the
     * LK proofs in gapt differ from the LK proofs in the XML format: the XML format
     * sees sequents in proofs as pairs of lists of formulas, while gapt sees sequents
     * in proofs as pairs of sets of formula occurrences. The parser converts the
     * XML proofs in such a way that the ancestor relation is preserved.
     *
     * TODO: prooflink parsing is not supported yet!
     *
     * @param n A &lt;proof&gt;, &lt;rule&gt;, or &lt;prooflink&gt; Node.
     * @return  An LKProof object corresponding to n.
     * @throws  ParsingException If n is not a &lt;proof&gt;, &lt;rule&gt; or &lt;prooflink&gt;
     * Node.
     */
    def getProof( n : Node ) : LKProof = getProofRec( n )._1

    // we parse the XML format to our LK
    // the difference is: our LK works on sequents which are defined as pairs of sets of formula occurrences
    //                    XML LK works on sequents which are defined as pairs of lists of formulas
    //
    // what we do is: we keep two arrays of formula occurrences, with the intended interpretation that
    // the i'th formula in the list in the sequent corresponds to the i'th formula occurrence in this array.
    //
    // using these arrays, we always know which formula occurrences to pass to the rule constructors.
    private def getProofRec( n : Node ) : (LKProof, Array[FormulaOccurrence], Array[FormulaOccurrence]) =
      trim(n) match {
        case <proof>{ ns @ _* }</proof> => {
          // TODO: read symbol, calculus
          getProofRec( ns.first )
        }
        case <rule>{ ns @ _* }</rule> => {
          val rt = n.attribute("type").get.first.text
          val param = if ( n.attribute("param") == None ) None else Some( n.attribute("param").get.first.text )
          val conc = ( new NodeReader(ns.first) with XMLSequentParser ).getSequent()
          // TODO: according to DTD, there may be a "substitution" element here
          // but I think it's not actually used.
          val substnodes = ns.filter( n => n.label == "lambdasubstitution" )
          val subst = if ( !substnodes.isEmpty )
                        Some((new NodeReader( substnodes.first ) with XMLSetTermParser).getSetTerm)
                      else
                        None
          val recl = ns.filter( n => n.label == "rule" ).map( n => getProofRec( n ) ).toList
          val prems = recl.map( p => p._1 )
          val l_perms = recl.map( p => p._2 )
          val r_perms = recl.map( p => p._3 )
          val triple = createRule( rt, conc, prems, l_perms, r_perms, param, subst )
          // check whether conclusion has been correctly constructed
          assert( triple._1.root.getSequent.multisetEquals( conc ) )
          // check whether the permutation of the formula occurrences corresponds to the conclusion
          def checkPerm( perm: Array[FormulaOccurrence], list: List[Formula] ) =
            perm.zip( perm.indices ).foreach( p => assert( p._1.formula == list.apply( p._2 ),
              "formula at occurrence " + p._1.formula.toStringSimple +
              " is not equal to formula in list position " + p._2 + ": " +
              list.apply( p._2 ).toStringSimple + " after creating rule of type " + rt
          ) )
          checkPerm( triple._2, conc.antecedent )
          checkPerm( triple._3, conc.succedent )
          triple
        }
        case <prooflink/> => {
          //n.attribute("symbol").get.first.text
          // TODO: create DAG Proof!?
          throw new ParsingException("Could not parse prooflink node (not supported yet): " + n.toString)
        }
        case _ => throw new ParsingException("Could not parse XML: " + n.toString)
      }

    // permutes m according to the permutation perm.
    private def permuteMap( perm: Int => Int, m: Array[FormulaOccurrence] ) =
    {
      val ret = new Array[FormulaOccurrence]( m.size )
      for ( i <- 0 until m.size ) { ret.update( perm( i ), m.apply( i ) ) }
      ret
    }

    private def createStrongContractionLeft(prem: LKProof, param: Array[Int], l_perm: Array[FormulaOccurrence], r_perm : Array[FormulaOccurrence]) : (LKProof, Array[FormulaOccurrence], Array[FormulaOccurrence]) =
      createStrongContraction( prem, param, l_perm, r_perm, ( l: Array[FormulaOccurrence], r: Array[FormulaOccurrence] ) => l, ContractionLeftRule.apply )

    private def createStrongContractionRight(prem: LKProof, param: Array[Int], l_perm: Array[FormulaOccurrence], r_perm : Array[FormulaOccurrence]) : (LKProof, Array[FormulaOccurrence], Array[FormulaOccurrence]) =
      createStrongContraction( prem, param, l_perm, r_perm, ( l: Array[FormulaOccurrence], r: Array[FormulaOccurrence] ) => r, ContractionRightRule.apply )

    // constructs a series of ContractionRules to simulate the "strong"
    // contraction rule of http://www.logic.at/ceres/downloads/calculus_LK.pdf
    //
    // function is parameterized to allow easy definition of right/left rules
    private def createStrongContraction(
      prem: LKProof, param: Array[Int], l_perm: Array[FormulaOccurrence], r_perm : Array[FormulaOccurrence], 
      side_chooser: (Array[FormulaOccurrence], Array[FormulaOccurrence]) => Array[FormulaOccurrence],
      rule_constructor: (LKProof, FormulaOccurrence, FormulaOccurrence) => LKProof 
    ) : (LKProof, Array[FormulaOccurrence], Array[FormulaOccurrence]) = {
      // check whether param is valid
      var sum = 0
      param.foreach( i => sum += i )
      assert( sum == side_chooser( l_perm, r_perm ).length )

      if ( param.filter( x => x > 1 ).isEmpty )
        (prem, l_perm, r_perm)
      else {
        val new_param = new Array[Int]( param.length )
        // init new_param
        for ( i <- 0 until param.length )
          new_param.update( i, param.apply( i ) )

        val pos = param.zip( param.indices ).filter( p => p._1 > 1 ).first._2

        new_param.update( pos, param.apply( pos ) - 1 )
        val auxf1 = side_chooser( l_perm, r_perm ).apply( pos )
        val auxf2 = side_chooser( l_perm, r_perm ).apply( pos + 1 )
        val rule = rule_constructor( prem, auxf1, auxf2 )
        val new_l_perm = l_perm.filter( o => o != auxf1 )
        val new_r_perm = r_perm.filter( o => o != auxf1 )
        assert( l_perm.length + r_perm.length == new_l_perm.length + new_r_perm.length + 1 )
        createStrongContraction( rule, new_param, new_l_perm.map( mapToDesc( rule ) ), new_r_perm.map( mapToDesc( rule ) ), side_chooser, rule_constructor )
      }
    }

    private def mapToDesc( r: LKProof )( o : FormulaOccurrence ) = r.getDescendantInLowerSequent( o ) match {
      case Some( d ) => d
      case None => throw new Exception("Expected to find formula occurrence descendant, but didn't!")
    }

    private def createRule( rt : String, conc: Sequent, prems: List[LKProof],
      l_perms: List[Array[FormulaOccurrence]], r_perms : List[Array[FormulaOccurrence]],
      param : Option[String], subst: Option[LambdaExpression] ) : 
      (LKProof, Array[FormulaOccurrence], Array[FormulaOccurrence]) = rt match {
        case "axiom" => {
          val a = Axiom(conc) // The Axiom factory provides the axiom and the initial map from 
                              // our lists of formulas to lists of formula occurrences
          ( a._1, a._2._1.toArray, a._2._2.toArray )
        }
        case "permr" => {
          if ( param == None )
            throw new ParsingException("Rule type is permr, but param attribute is not present.")
          val param_s = param.get
          val prem = prems.first
          val l_perm = l_perms.first
          val r_perm = r_perms.first
          ( prem, l_perm, permuteMap( XMLUtils.permStringToFun( param_s, prem.root.succedent.size ), r_perm ) )
        }
        case "perml" => {
          if ( param == None )
            throw new ParsingException("Rule type is perml, but param attribute is not present.")
          val param_s = param.get
          val prem = prems.first
          val r_perm = r_perms.first
          val l_perm = l_perms.first
          ( prem, permuteMap( XMLUtils.permStringToFun( param_s, prem.root.antecedent.size ), l_perm ), r_perm )
        }
        case "contrl" => {
          if ( param == None )
            throw new ParsingException("Rule type is contrl, but param attribute is not present.")
          val c_param = param.get.split(',').map( s => s.toInt ).toArray
          val prem = prems.first
          val r_perm = r_perms.first
          val l_perm = l_perms.first
          createStrongContractionLeft(prem, c_param, l_perm, r_perm)
        }
        case "contrr" => {
          if ( param == None )
            throw new ParsingException("Rule type is contrr, but param attribute is not present.")
          val c_param = param.get.split(',').map( s => s.toInt ).toArray
          val prem = prems.first
          val r_perm = r_perms.first
          val l_perm = l_perms.first
          createStrongContractionRight(prem, c_param, l_perm, r_perm)
        }
        case "weakl" => {
          // TODO: in principle, the calculus definition allows introduction of more than
          // one weak formula. Is this used in practice?
          val prem = prems.first
          val r_perm = r_perms.first
          val l_perm = l_perms.first
          val weakf = conc.antecedent.first
          val rule = WeakeningLeftRule( prem, weakf )
          // TODO: prin.first is redundant, we know that WeakeningLeftRule has only one main formula
          ( rule, (List( rule.prin.first ) ++ ( l_perm.map( mapToDesc( rule ) ) ) ).toArray, r_perm.map( mapToDesc( rule ) ) )
        }
        case "weakr" => {
          // TODO: in principle, the calculus definition allows introduction of more than
          // one weak formula. Is this used in practice?
          val prem = prems.first
          val r_perm = r_perms.first
          val l_perm = l_perms.first
          val weakf = conc.succedent.last
          val rule = WeakeningRightRule( prem, weakf )
          // TODO: prin.first is redundant, we know that WeakeningLeftRule has only one main formula
          ( rule, l_perm.map( mapToDesc( rule ) ), ( r_perm.map( mapToDesc( rule ) ) ++ List( rule.prin.first ) ).toArray )
        }
        case "cut" => {
          val l_prem = prems.first
          val r_prem = prems.last
          val l_perm_l = l_perms.first
          val l_perm_r = r_perms.first
          def r_perm_l = l_perms.last
          def r_perm_r = r_perms.last
          val l_p_s = l_prem.root.succedent.size
          val auxf_l = l_perm_r.last
          val auxf_r = r_perm_l.first
          val rule = CutRule( l_prem, r_prem, auxf_l, auxf_r )
          ( rule,
            ( (l_perm_l.map( mapToDesc( rule ) ) ) ++ 
            r_perm_l.drop( 1 ).map( mapToDesc( rule ) ) ).toArray,
            ( l_perm_r.take( l_perm_r.size - 1 ).map( mapToDesc( rule ) ) ++ 
            r_perm_r.map( mapToDesc( rule ) ) ).toArray )
        }
        case "andr" => {
          val l_prem = prems.first
          val r_prem = prems.last
          def l_perm_l = l_perms.first
          def l_perm_r = r_perms.first
          def r_perm_l = l_perms.last
          def r_perm_r = r_perms.last
          val l_p_s = l_prem.root.succedent.size
          val r_p_s = r_prem.root.succedent.size 
          val auxf_l = l_perm_r.last
          val auxf_r = r_perm_r.last
          val rule = AndRightRule( l_prem, r_prem, auxf_l, auxf_r )
          ( rule,
            l_perm_l.map( mapToDesc( rule ) ) ++ r_perm_l.map( mapToDesc( rule ) ),
            ( l_perm_r.take( l_perm_r.size - 1 ).map( mapToDesc( rule ) ) ++ 
            r_perm_r.map( mapToDesc( rule ) ) ).toArray )
        }
        case "orl" => {
          val l_prem = prems.first
          val r_prem = prems.last
          def l_perm_l = l_perms.first
          def l_perm_r = r_perms.first
          def r_perm_l = l_perms.last
          def r_perm_r = r_perms.last
          val auxf_l = l_perm_l.first
          val auxf_r = r_perm_l.first
          val rule = OrLeftRule( l_prem, r_prem, auxf_l, auxf_r )
          ( rule,
            l_perm_l.map( mapToDesc( rule ) ) ++ r_perm_l.drop( 1 ).map( mapToDesc( rule ) ),
            l_perm_r.map( mapToDesc( rule ) ) ++ r_perm_r.map( mapToDesc( rule ) ) )
        }
        case "impll" => {
          val l_prem = prems.first
          val r_prem = prems.last
          val l_perm_l = l_perms.first
          val l_perm_r = r_perms.first
          def r_perm_l = l_perms.last
          def r_perm_r = r_perms.last
          val l_p_s = l_prem.root.succedent.size
          val auxf_l = l_perm_r.last
          val auxf_r = r_perm_l.first
          val rule = ImpLeftRule( l_prem, r_prem, auxf_l, auxf_r )
          // TODO: prin.first is redundant, we know that ImpLeftRule has only one main formula
          ( rule,
            ( List( rule.prin.first ) ++ (l_perm_l.map( mapToDesc( rule ) ) ) ++ 
            r_perm_l.drop( 1 ).map( mapToDesc( rule ) ) ).toArray,
            ( l_perm_r.take( l_perm_r.length - 1 ).map( mapToDesc( rule ) ) ++ 
            r_perm_r.map( mapToDesc( rule ) ) ).toArray )
        }
        case "implr" => {
          val prem = prems.first
          val l_perm = l_perms.first
          val r_perm = r_perms.first
          val auxf1 = l_perm.first
          val auxf2 = r_perm.last
          val rule = ImpRightRule( prem, auxf1, auxf2 )
          ( rule, ( l_perm.drop( 1 ).map( mapToDesc( rule ) ) ).toArray, r_perm.map( mapToDesc( rule ) ) )
        }
        case "negr" => {
          val prem = prems.first
          val l_perm = l_perms.first
          val r_perm = r_perms.first
          val auxf = l_perm.first
          val rule = NegRightRule( prem, auxf )
          // TODO: prin.first is redundant, we know that NegRightRule has only one main formula
          ( rule, ( l_perm.drop( 1 ).map( mapToDesc( rule ) ) ).toArray,
            ( r_perm.map( mapToDesc( rule ) ) ++ List( rule.prin.first ) ).toArray )
        }
        case "negl" => {
          val prem = prems.first
          val l_perm = l_perms.first
          val r_perm = r_perms.first
          val auxf = r_perm.last
          val rule = NegLeftRule( prem, auxf )
          // TODO: prin.first is redundant, we know that NegRightRule has only one main formula
          ( rule, ( List( rule.prin.first ) ++ l_perm.map( mapToDesc( rule ) ) ).toArray, 
            ( r_perm.take( r_perm.length - 1 ).map( mapToDesc( rule ) ) ).toArray )
        }
        case "orr1" => {
          val prem = prems.first
          val l_perm = l_perms.first
          val r_perm = r_perms.first
          val auxf = r_perm.last
          val mainf = conc.succedent.last
          val rule = mainf match {
            case Or(_, weakf) => OrRight1Rule( prem, auxf, weakf )
            case _ => throw new ParsingException("Rule type is orr1, but main formula is not a disjunction.")
          }
          ( rule, l_perm.map( mapToDesc( rule ) ), r_perm.map( mapToDesc( rule ) ) )
        }
        case "orr2" => {
          val prem = prems.first
          val l_perm = l_perms.first
          val r_perm = r_perms.first
          val auxf = r_perm.last
          val mainf = conc.succedent.last
          val rule = mainf match {
            case Or(weakf, _) => OrRight2Rule( prem, weakf, auxf )
            case _ => throw new ParsingException("Rule type is orr2, but main formula is not a disjunction.")
          }
          ( rule, l_perm.map( mapToDesc( rule ) ), r_perm.map( mapToDesc( rule ) ) )
        }
        case "andl1" => {
          val prem = prems.first
          val l_perm = l_perms.first
          val r_perm = r_perms.first
          val auxf = l_perm.first
          val mainf = conc.antecedent.first
          val rule = mainf match {
            case And(_, weakf) => AndLeft1Rule( prem, auxf, weakf )
            case _ => throw new ParsingException("Rule type is andl1, but main formula is not a conjunction.")
          }
          ( rule, l_perm.map( mapToDesc( rule ) ), r_perm.map( mapToDesc( rule ) ) )
        }
        case "andl2" => {
          val prem = prems.first
          val l_perm = l_perms.first
          val r_perm = r_perms.first
          val auxf = l_perm.first
          val mainf = conc.antecedent.first
          val rule = mainf match {
            case And(weakf, _) => AndLeft2Rule( prem, weakf, auxf )
            case _ => throw new ParsingException("Rule type is andl2, but main formula is not a conjunction.")
          }
          ( rule, l_perm.map( mapToDesc( rule ) ), r_perm.map( mapToDesc( rule ) ) )
        }
        case "foralll" => {
          val prem = prems.first
          val l_perm = l_perms.first
          val r_perm = r_perms.first
          val auxf = l_perm.first
          val mainf = conc.antecedent.first
          val rule = mainf match {
            // TODO: give auxf instead of auxf.formula
            // TODO: compute substitution term by unification, right now: dummy variable "a"
            case All(sub) => ForallLeftRule( prem, auxf.formula, mainf, HOLVar(new VariableStringSymbol("a"), i) )
            case _ => throw new ParsingException("Rule type is foralll, but main formula is not all-quantified.")
          }
          ( rule, l_perm.map( mapToDesc( rule ) ), r_perm.map( mapToDesc( rule ) ) )
        }
        case "foralll2" => {
          val prem = prems.first
          val l_perm = l_perms.first
          val r_perm = r_perms.first
          val auxf = l_perm.first
          val mainf = conc.antecedent.first
          val rule = mainf match {
            // TODO: give auxf instead of auxf.formula
            case All(sub) => ForallLeftRule( prem, auxf.formula, mainf, subst.get )
            case _ => throw new ParsingException("Rule type is foralll2, but main formula is not all-quantified.")
          }
          ( rule, l_perm.map( mapToDesc( rule ) ), r_perm.map( mapToDesc( rule ) ) )
        }
        case "existsl" => {
          val prem = prems.first
          val l_perm = l_perms.first
          val r_perm = r_perms.first
          val auxf = l_perm.first
          val mainf = conc.antecedent.first
          val rule = mainf match {
            // TODO: give auxf instead of auxf.formula
            // TODO: compute eigenvar by unification, right now: dummy variable "a"
            case Ex(sub) => ExistsLeftRule( prem, auxf.formula, mainf, HOLVar(new VariableStringSymbol("a"), i) )
            case _ => throw new ParsingException("Rule type is existsl, but main formula is not ex-quantified.")
          }
          ( rule, l_perm.map( mapToDesc( rule ) ), r_perm.map( mapToDesc( rule ) ) )
        }
        case "existsl2" => {
          val prem = prems.first
          val l_perm = l_perms.first
          val r_perm = r_perms.first
          val auxf = l_perm.first
          val mainf = conc.antecedent.first
          val rule = mainf match {
            // TODO: give auxf instead of auxf.formula
            // TODO: compute eigenvar by unification, right now: dummy variable "a"
            case Ex(sub) => ExistsLeftRule( prem, auxf.formula, mainf, HOLVar(new VariableStringSymbol("a"), i -> o) )
            case _ => throw new ParsingException("Rule type is existsl, but main formula is not ex-quantified.")
          }
          ( rule, l_perm.map( mapToDesc( rule ) ), r_perm.map( mapToDesc( rule ) ) )
        }
        case "forallr" => {
          val prem = prems.first
          val l_perm = l_perms.first
          val r_perm = r_perms.first
          val auxf = r_perm.last
          val mainf = conc.succedent.last
          val rule = mainf match {
            // TODO: give auxf instead of auxf.formula
            // TODO: compute eigenvar by unification, right now: dummy variable "a"
            case All(sub) => ForallRightRule( prem, auxf.formula, mainf, HOLVar(new VariableStringSymbol("a"), i) )
            case _ => throw new ParsingException("Rule type is forallr, but main formula is not all-quantified.")
          }
          ( rule, l_perm.map( mapToDesc( rule ) ), r_perm.map( mapToDesc( rule ) ) )
        }
        case "forallr2" => {
          val prem = prems.first
          val l_perm = l_perms.first
          val r_perm = r_perms.first
          val auxf = r_perm.last
          val mainf = conc.succedent.last
          val rule = mainf match {
            // TODO: give auxf instead of auxf.formula
            // TODO: compute eigenvar by unification, right now: dummy variable "a"
            case All(sub) => ForallRightRule( prem, auxf.formula, mainf, HOLVar(new VariableStringSymbol("a"), i -> o) )
            case _ => throw new ParsingException("Rule type is forallr, but main formula is not all-quantified.")
          }
          ( rule, l_perm.map( mapToDesc( rule ) ), r_perm.map( mapToDesc( rule ) ) )
        }
        case "existsr" => {
          val prem = prems.first
          val l_perm = l_perms.first
          val r_perm = r_perms.first
          val auxf = r_perm.last
          val mainf = conc.succedent.last
          val rule = mainf match {
            // TODO: give auxf instead of auxf.formula
            // TODO: compute substitution term by unification, right now: dummy variable "a"
            case Ex(sub) => ExistsRightRule( prem, auxf.formula, mainf, HOLVar(new VariableStringSymbol("a"), i) )
            case _ => throw new ParsingException("Rule type is existsr, but main formula is not ex-quantified.")
          }
          ( rule, l_perm.map( mapToDesc( rule ) ), r_perm.map( mapToDesc( rule ) ) )
        }
        case "existsr2" => {
          val prem = prems.first
          val l_perm = l_perms.first
          val r_perm = r_perms.first
          val auxf = r_perm.last
          val mainf = conc.succedent.last
          val rule = mainf match {
            // TODO: give auxf instead of auxf.formula
            case Ex(sub) => ExistsRightRule( prem, auxf.formula, mainf, subst.get )
            case _ => throw new ParsingException("Rule type is existsr, but main formula is not ex-quantified.")
          }
          ( rule, l_perm.map( mapToDesc( rule ) ), r_perm.map( mapToDesc( rule ) ) )
        }
        case "defl" => {
          val prem = prems.first
          val l_perm = l_perms.first
          val r_perm = r_perms.first
          val auxf = l_perm.first
          val mainf = conc.antecedent.first
          val rule = DefinitionLeftRule( prem, auxf.formula, mainf )
          // TODO: give auxf instead of auxf.formula
          ( rule, l_perm.map( mapToDesc( rule ) ), r_perm.map( mapToDesc( rule ) ) )
        }
        case "defr" => {
          val prem = prems.first
          val l_perm = l_perms.first
          val r_perm = r_perms.first
          val auxf = r_perm.last
          val mainf = conc.succedent.last
          val rule = DefinitionRightRule( prem, auxf.formula, mainf )
          // TODO: give auxf instead of auxf.formula
          ( rule, l_perm.map( mapToDesc( rule ) ), r_perm.map( mapToDesc( rule ) ) )
        }
        case "eql1" => {
          val l_prem = prems.first
          val r_prem = prems.last
          def l_perm_l = l_perms.first
          def l_perm_r = r_perms.first
          def r_perm_l = l_perms.last
          def r_perm_r = r_perms.last
          val l_p_s = l_prem.root.succedent.size
          val r_p_s = r_prem.root.succedent.size 
          val auxf_l = l_perm_r.last
          val auxf_r = r_perm_l.first
          val mainf = conc.antecedent.first
          // TODO: parse and pass parameter
          val rule = EquationLeft1Rule( l_prem, r_prem, auxf_l, auxf_r, mainf )
          ( rule,
            ( List( rule.prin.first ) ++ (l_perm_l.map( mapToDesc( rule ) ) ) ++ 
            r_perm_l.drop( 1 ).map( mapToDesc( rule ) ) ).toArray,
            ( l_perm_r.take( l_perm_r.length - 1 ).map( mapToDesc( rule ) ) ++ 
            r_perm_r.map( mapToDesc( rule ) ) ).toArray )
        }
        case "eql2" => {
          val l_prem = prems.first
          val r_prem = prems.last
          def l_perm_l = l_perms.first
          def l_perm_r = r_perms.first
          def r_perm_l = l_perms.last
          def r_perm_r = r_perms.last
          val l_p_s = l_prem.root.succedent.size
          val r_p_s = r_prem.root.succedent.size 
          val auxf_l = l_perm_r.last
          val auxf_r = r_perm_l.first
          val mainf = conc.antecedent.first
          // TODO: parse and pass parameter
          val rule = EquationLeft2Rule( l_prem, r_prem, auxf_l, auxf_r, mainf )
          ( rule,
            ( List( rule.prin.first ) ++ (l_perm_l.map( mapToDesc( rule ) ) ) ++ 
            r_perm_l.drop( 1 ).map( mapToDesc( rule ) ) ).toArray,
            ( l_perm_r.take( l_perm_r.length - 1 ).map( mapToDesc( rule ) ) ++ 
            r_perm_r.map( mapToDesc( rule ) ) ).toArray )
        }
        case "eqr1" => {
          val l_prem = prems.first
          val r_prem = prems.last
          def l_perm_l = l_perms.first
          def l_perm_r = r_perms.first
          def r_perm_l = l_perms.last
          def r_perm_r = r_perms.last
          val l_p_s = l_prem.root.succedent.size
          val r_p_s = r_prem.root.succedent.size 
          val auxf_l = l_perm_r.last
          val auxf_r = r_perm_r.last
          val mainf = conc.succedent.last
          // TODO: parse and pass parameter
          val rule = EquationRight1Rule( l_prem, r_prem, auxf_l, auxf_r, mainf )
          ( rule,
            ( l_perm_l.map( mapToDesc( rule ) ) ++ 
            r_perm_l.map( mapToDesc( rule ) ) ).toArray,
            ( l_perm_r.take( l_perm_r.length - 1 ).map( mapToDesc( rule ) ) ++ 
            r_perm_r.map( mapToDesc( rule ) ) ).toArray )
        }
        case "eqr2" => {
          val l_prem = prems.first
          val r_prem = prems.last
          def l_perm_l = l_perms.first
          def l_perm_r = r_perms.first
          def r_perm_l = l_perms.last
          def r_perm_r = r_perms.last
          val l_p_s = l_prem.root.succedent.size
          val r_p_s = r_prem.root.succedent.size 
          val auxf_l = l_perm_r.last
          val auxf_r = r_perm_r.last
          val mainf = conc.succedent.last
          // TODO: parse and pass parameter
          val rule = EquationRight2Rule( l_prem, r_prem, auxf_l, auxf_r, mainf )
          ( rule,
            ( l_perm_l.map( mapToDesc( rule ) ) ++ 
            r_perm_l.map( mapToDesc( rule ) ) ).toArray,
            ( l_perm_r.take( l_perm_r.length - 1 ).map( mapToDesc( rule ) ) ++ 
            r_perm_r.map( mapToDesc( rule ) ) ).toArray )
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
  
  /**
   * This trait parses XML elements subsumed under the &amp;formula; entity into their
   * respective objects.
   */
  trait XMLFormulaParser extends XMLNodeParser {
    /**
     * If the Node provided by XMLNodeParser is one of the elements defined by the
     * &amp;formula; entity, a HOLFormula object corresponding to the Node is returned.
     *
     * @return An HOLFormula object corresponding to the Node provided by getInput().
     * @throws ParsingException If the Node provided by getInput() is not one of the elements
     *                          defined by the &amp;formula; entity.
     */
    def getFormula() : HOLFormula = getFormula( getInput() )

    /**
     * If n is one of the elements defined by the
     * &amp;formula; entity, a HOLFormula object corresponding to the Node is returned.
     *
     * @param n A Node corresponding to an element defined by the &amp;formula; entity.
     * @return An HOLFormula object corresponding to the Node provided by getInput().
     * @throws ParsingException If n is not one of the elements
     *                          defined by the &amp;formula; entity.
     */
    def getFormula(n : Node) : HOLFormula =
      trim(n) match {
        case <constantatomformula>{ ns @ _* }</constantatomformula>
          => Atom(new ConstantStringSymbol( n.attribute("symbol").get.first.text ),
                  XMLUtils.nodesToAbstractTerms(ns.toList))
        case <variableatomformula>{ ns @ _* }</variableatomformula>
          => AppN( (new NodeReader( ns.first ) with XMLSetTermParser).getSetTerm(),
                   XMLUtils.nodesToAbstractTerms( ns.toList.tail ) ).asInstanceOf[HOLFormula]
        case <definedsetformula>{ ns @ _* }</definedsetformula>
          => AppN( (new NodeReader( ns.first ) with XMLSetTermParser).getSetTerm(),
                   XMLUtils.nodesToAbstractTerms( ns.toList.tail ) ).asInstanceOf[HOLFormula]
        case <conjunctiveformula>{ ns @ _* }</conjunctiveformula> 
          => createConjunctiveFormula(n.attribute("type").get.first.text,
                                         XMLUtils.nodesToFormulas(ns.toList))
        case <quantifiedformula>{ ns @ _* }</quantifiedformula> =>
        {
                  val variable = ( new NodeReader(ns.first) with XMLTermParser).getVariable()
                  val form = ( new NodeReader(ns.last) with XMLFormulaParser).getFormula() 
                  createQuantifiedFormula( n.attribute("type").get.first.text,
                                           variable, form )
        }
        case <secondorderquantifiedformula>{ ns @ _*}</secondorderquantifiedformula> =>
        {
          val variable = ( new NodeReader(ns.first) with XMLSetTermParser).getSetTerm().asInstanceOf[HOLVar]
          val form = ( new NodeReader(ns.last) with XMLFormulaParser).getFormula()
          createQuantifiedFormula( n.attribute("type").get.first.text,
                                              variable, form )

        }
        case _ => throw new ParsingException("Could not parse XML: " + n.toString)
      }

    private def createConjunctiveFormula(sym: String, formulas: List[HOLFormula]) : HOLFormula =
    {
      sym match {
        case "and" => And(formulas.first, formulas.last)
        case "or" => Or(formulas.first, formulas.last)
        case "impl" => Imp(formulas.first, formulas.last)
        case "neg" => Neg(formulas.first)
        case _ => throw new ParsingException("Could not parse conjunctiveformula type: " + sym)
      }
    }

    private def createQuantifiedFormula(sym: String, variable: HOLVar, formula: HOLFormula) : HOLFormula =
      sym match {
        case "all" => AllVar(variable, formula)
        case "exists" => ExVar(variable, formula)
        case "all2" => AllVar(variable, formula)
        case "exists2" => ExVar(variable, formula)
        case _ => throw new ParsingException("Could not parse quantifiedformula type: " + sym)
      }
  }
  
/**
 * This trait parses the elements subsumed under the entity &amp;abstractterm;
 */
  trait XMLAbstractTermParser extends XMLNodeParser {
    /**
     * If the Node provided by XMLNodeParser is one of the elements defined by the
     * &amp;abstractterm; entity, a HOLTerm object corresponding to the Node is returned.
     *
     * @return An HOLTerm object corresponding to the Node provided by getInput().
     * @throws ParsingException If the Node provided by getInput() is not one of the elements
     *                          defined by the &amp;abstractterm; entity.
     */
    def getAbstractTerm() : HOLTerm = getAbstractTerm( getInput() )

    /**
     * If n is one of the elements defined by the
     * &amp;abstractterm; entity, a HOLTerm object corresponding to the Node is returned.
     *
     * @param n A Node corresponding to an element defined by the &amp;abstractterm; entity.
     * @return An HOLTerm object corresponding to the Node provided by getInput().
     * @throws ParsingException If n is not one of the elements
     *                          defined by the &amp;abstractterm; entity.
     */
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

/**
 * This trait parses the elements subsumed under the entity &amp;term;
 */
  trait XMLTermParser extends XMLNodeParser {
    /**
     * If the Node provided by XMLNodeParser is one of the elements defined by the
     * &amp;term; entity, a HOLTerm object corresponding to the Node is returned.
     *
     * @return A HOLTerm object corresponding to the Node provided by getInput().
     * @throws ParsingException If the Node provided by getInput() is not one of the elements
     *                          defined by the &amp;term; entity.
     */
    def getTerm() : HOLTerm = getTerm(getInput())

    /**
     * If the Node provided by XMLNodeParser is a &lt;variable&gt; element,
     * a HOLVar object corresponding to the Node is returned.
     *
     * @return A HOLVar object corresponding to the Node provided by getInput().
     * @throws ParsingException If the Node provided by getInput() is not a &lt;variable&gt; element.
     */
    def getVariable() : HOLVar = getVariable(getInput())

    /**
     * If n is a &lt;variable&gt; element, a HOLVar object corresponding to the Node is returned.
     *
     * @param n A Node corresponding to a &lt;variable&gt; element.
     * @return A HOLVar object corresponding to the Node provided by getInput().
     * @throws ParsingException If n is not a &lt;variable&gt; element.
     */
    def getVariable(n: Node) : HOLVar = try {
      getTerm(n).asInstanceOf[HOLVar]
    }
    catch {
      case e : ClassCastException => throw new ParsingException("Expected <variable> but found: " + n.toString)
    }

    /**
     * If n is one of the elements defined by the
     * &amp;term; entity, a HOLTerm object corresponding to the Node is returned.
     *
     * @param n A Node corresponding to an element defined by the &amp;term; entity.
     * @return A HOLTerm object corresponding to the Node provided by getInput().
     * @throws ParsingException If n is not one of the elements
     *                          defined by the &amp;term; entity.
     */
    def getTerm(n: Node) : HOLTerm =
      trim(n) match {
        case <variable/> => HOLVar(new VariableStringSymbol( n.attribute("symbol").get.first.text ), Ti() )
        case <constant/> => HOLConst(new ConstantStringSymbol( n.attribute("symbol").get.first.text ), Ti() )
        case <function>{ ns @ _* }</function> => createFunction(n.attribute("symbol").get.first.text,
                                                             XMLUtils.nodesToAbstractTerms(ns.toList))
        case _ => throw new ParsingException("Could not parse XML: " + n.toString)
      }
    private def createFunction( sym: String, args : List[HOLTerm] ) : HOLTerm =
      AppN( HOLConst(new ConstantStringSymbol(sym), FunctionType( Ti(), args.map( a => a.exptype ) ) ),
            args )
  }

/**
 * This trait parses the elements subsumed under the entity &amp;setterm;
 */
  trait XMLSetTermParser extends XMLNodeParser {
    /**
     * If the Node provided by XMLNodeParser is one of the elements defined by the
     * &amp;setterm; entity, a HOLTerm object corresponding to the Node is returned.
     *
     * @return A HOLTerm object corresponding to the Node provided by getInput().
     * @throws ParsingException If the Node provided by getInput() is not one of the elements
     *                          defined by the &amp;setterm; entity.
     */
    def getSetTerm() : HOLTerm = getSetTerm(getInput())

     /**
     * If n is one of the elements defined by the
     * &amp;setterm; entity, a HOLTerm object corresponding to the Node is returned.
     *
     * @param n A Node corresponding to an element defined by the &amp;setterm; entity.
     * @return A HOLTerm object corresponding to the Node provided by getInput().
     * @throws ParsingException If n is not one of the elements
     *                          defined by the &amp;setterm; entity.
     */ 
    def getSetTerm(n: Node) : HOLTerm =
      trim(n) match {
        // FIXME: the arity of the second-order variable is not
        // provided here, so we assume for the moment that all second order
        // variables have type i -> o.
        case <secondordervariable/> => 
          HOLVar(new VariableStringSymbol( n.attribute("symbol").get.first.text ),
                   i -> o)
        case <lambdasubstitution>{ ns @ _* }</lambdasubstitution> => {
          AbsN( (new NodeReader(ns.first) with XMLVariableListParser).getVariableList(),
                (new NodeReader(ns.last) with XMLFormulaParser).getFormula() )
        }
        // TODO: treat definitional aspect of definedset
        case <definedset>{ ns @ _* }</definedset> =>
        {
          val args = XMLUtils.nodesToAbstractTerms( ns.toList )
          AppN( HOLConst(new ConstantStringSymbol( n.attribute("symbol").get.first.text ),
                         FunctionType( i -> o, args.map( t => t.exptype ) ) ),
                args )
        }
        case _ => throw new ParsingException("Could not parse XML: " + n.toString)
      }
  }

   /**
   * This trait parses XML elements &lt;variablelist&gt; into Lists of HOLVar objects.
   */ 
  trait XMLVariableListParser extends XMLNodeParser {
    /**
     * If the Node provided by XMLNodeParser is a &lt;variablelist&gt; element,
     * a List of HOLVar objects corresponding to the Node is returned.
     *
     * @return A List of HOLVar objects corresponding to the Node provided by getInput().
     * @throws ParsingException If the Node provided by getInput() is not a &lt;variablelist&gt; element.
     */
    def getVariableList() : List[HOLVar] = getVariableList(getInput())

     /**
     * If n is a &lt;variablelist&gt; element,
     * a List of HOLVar objects corresponding to the Node is returned.
     *
     * @param n A Node correspondign to a &lt;variablelist&gt; element.
     * @return  A List of HOLVar objects corresponding to n.
     * @throws  ParsingException If n) is not a &lt;variablelist&gt; element.
     */   
    def getVariableList(n: Node) : List[HOLVar] =
      trim(n) match {
        case <variablelist>{ns @ _*}</variablelist> => {
          ns.map( n => (new NodeReader(n) with XMLTermParser).getVariable() ).toList
        }
        case _ => throw new ParsingException("Could not parse XML: " + n.toString)
      }
  }
}
