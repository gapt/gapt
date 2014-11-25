package at.logic.integration_tests

import java.io.{File, IOException}

import at.logic.algorithms.fol.hol2fol.{replaceAbstractions, reduceHolToFol}
import at.logic.algorithms.fol.recreateWithFactory
import at.logic.algorithms.hlk.HybridLatexParser
import at.logic.algorithms.lk.{AtomicExpansion, regularize}
import at.logic.algorithms.resolution.RobinsonToRal
import at.logic.algorithms.rewriting.DefinitionElimination
import at.logic.calculi.lk.base.{LKProof, FSequent}
import at.logic.calculi.lksk.sequentToLabelledSequent
import at.logic.calculi.resolution.robinson.RobinsonResolutionProof
import at.logic.language.fol.{FOLVar, FOLFormula, FOLExpression}
import at.logic.language.hol._
import at.logic.language.lambda.symbols.StringSymbol
import at.logic.language.lambda.types.{Ti, FunctionType, To, TA}
import at.logic.language.lambda.{Substitution => LambdaSubstitution, FactoryA, LambdaExpression, Var}

import at.logic.provers.prover9._
import at.logic.transformations.ceres.clauseSets.{AlternativeStandardClauseSet, StandardClauseSet}
import at.logic.transformations.ceres.projections.Projections
import at.logic.transformations.ceres.struct.StructCreators

import at.logic.transformations.ceres.{ceres_omega, CERES, CERESR2LK}
import at.logic.transformations.skolemization.lksk.LKtoLKskc
import at.logic.utils.testing.ClasspathFileCopier

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class nTapeTest extends SpecificationWithJUnit with ClasspathFileCopier {
  val box = List()
  def checkForProverOrSkip = Prover9.refute(box) must not(throwA[IOException]).orSkip

  def show(s:String) = println("+++++++++ "+s+" ++++++++++")


  object Robinson2RalAndUndoHOL2Fol {
    def apply(sig_vars : Map[String, List[HOLVar]],
              sig_consts : Map[String, List[HOLConst]],
              cmap : replaceAbstractions.ConstantsMap) =
      new Robinson2RalAndUndoHOL2Fol(sig_vars, sig_consts, cmap)


    def backtranslate(e:FOLFormula,
                      sig_vars : Map[String, List[HOLVar]],
                      sig_consts : Map[String, List[HOLConst]],
                      abssymbol_map : Map[String, HOLExpression])(factory : FactoryA) : HOLFormula =
      backtranslate(e.asInstanceOf[FOLExpression], sig_vars, sig_consts, abssymbol_map, Some(To))(factory).asInstanceOf[HOLFormula]

    /**
     * We do some dirty stuff in here to translate a prover9 term back to the richer type signature of hol proofs, undoing
     * replace abstractions at the same time.
     */
    def backtranslate(e:FOLExpression,
                      sig_vars : Map[String, List[HOLVar]],
                      sig_consts : Map[String, List[HOLConst]],
                      abssymbol_map : Map[String, HOLExpression],
                      expected_type : Option[TA])(factory : FactoryA) : HOLExpression = {
      import at.logic.language.fol

      e match {
        // --------------- logical structure ------------------------
        case fol.Atom(name, args) if sig_consts contains name.toString =>
          val args_ = args.map(backtranslate(_, sig_vars, sig_consts, abssymbol_map, None)(factory))
          val head = sig_consts(name.toString)(0)
          Atom(head, args_)

        case fol.Neg(f) => Neg(backtranslate(f, sig_vars, sig_consts, abssymbol_map)(factory))
        case fol.And(f,g) => And(backtranslate(f, sig_vars, sig_consts, abssymbol_map)(factory),backtranslate(g, sig_vars, sig_consts, abssymbol_map)(factory))
        case fol.Or(f,g) => Or(backtranslate(f, sig_vars, sig_consts, abssymbol_map)(factory),backtranslate(g, sig_vars, sig_consts, abssymbol_map)(factory))
        case fol.Imp(f,g) => Imp(backtranslate(f, sig_vars, sig_consts, abssymbol_map)(factory),backtranslate(g, sig_vars, sig_consts, abssymbol_map)(factory))
        case fol.AllVar(x,f) =>
          val f_ = backtranslate(f, sig_vars, sig_consts, abssymbol_map)(factory)
          val xcandidates = freeVariables(f_).filter(_.name == x.name)
          xcandidates match {
            case Nil => AllVar(factory.createVar(x.sym, x.exptype).asInstanceOf[HOLVar], f_)
            case List(x_) => AllVar(x_, f_)
            case _ => throw new Exception("We have not more than one free variable with name "+x.name+xcandidates.mkString(": (",", ",")"))
          }

        case fol.ExVar(x,f) =>
          val f_ = backtranslate(f, sig_vars, sig_consts, abssymbol_map)(factory)
          val xcandidates = freeVariables(f_).filter(_.name == x.name)
          xcandidates match {
            case Nil => ExVar(factory.createVar(x.sym, x.exptype).asInstanceOf[HOLVar], f_)
            case List(x_) => ExVar(x_, f_)
            case _ => throw new Exception("We have not more than one free variable with name "+x.name+xcandidates.mkString(": (",", ",")"))
          }


        // --------------- term structure ------------------------
        //cases for term replacement
        case HOLConst(name, _) if abssymbol_map.contains(name) =>
          val qterm = recreateWithFactory(abssymbol_map(name), factory).asInstanceOf[HOLExpression] //unsafe cast
          expected_type match {
            case Some(expt) =>
              require(qterm.exptype == expt, "We did a replacement of the symbol "+name+" by "+qterm+" but the type "+qterm.exptype+" is not the expected type "+expected_type)
              qterm
            case None =>
              qterm
          }

        case Function(HOLConst(name, _), args, _) if abssymbol_map.contains(name) =>
          val qterm = recreateWithFactory(abssymbol_map(name), factory).asInstanceOf[HOLExpression] //unsafe cast
        val btargs = args.map(x => backtranslate(x.asInstanceOf[FOLExpression],sig_vars, sig_consts, abssymbol_map, None)(factory))
          val r = btargs.foldLeft(qterm)((term, nextarg) => HOLApp(term, nextarg))
          expected_type match {
            case Some(expt) =>
              require(qterm.exptype == expt, "We did a replacement of the symbol "+name+" by "+qterm+" but the type "+qterm.exptype+" is not the expected type "+expected_type)
              qterm
            case None =>
              qterm
          }

        //normal ones
        case Function(HOLConst(name,_), args, _) if sig_consts contains name =>
          val btargs = args.map(x => backtranslate(x.asInstanceOf[FOLExpression],sig_vars, sig_consts, abssymbol_map, None)(factory))
          val head = sig_consts(name)(0) //we have to pick a candidate somehow, lets go for the first
          Function(head, btargs)

        case fol.FOLVar(name) if sig_vars contains name =>
          val head = sig_vars(name)(0) //we have to pick a candidate somehow, lets go for the first
          head

        case fol.FOLConst(name) if sig_consts contains name =>
          val head = sig_consts(name)(0) //we have to pick a candidate somehow, lets go for the first
          head

        case fol.FOLVar(ivy_varname(name) ) =>
          println("Guessing that the variable "+name+" comes from ivy, assigning type i.")
          factory.createVar(StringSymbol(name), Ti).asInstanceOf[HOLVar]

        case fol.FOLVar(name) =>
          throw new Exception("No signature information for variable "+e)

        case fol.FOLConst(name) =>
          throw new Exception("No signature information for const "+e)

        case _ =>
          throw new Exception("Could not convert subterm "+e)



      }
    }

    val ivy_varname = """(v[0-9]+)""".r


    def getSignature(fs:List[HOLExpression])  : (Map[String,Set[HOLConst]], Map[String, Set[HOLVar]]) =
      fs.foldLeft((Map[String,Set[HOLConst]](), Map[String, Set[HOLVar]]()))( (maps, e) => {
        //println("next "+maps._1.size+":"+maps._2.size)
        getSignature(e, maps._1, maps._2)
      }
      )

    def getSignature(e:HOLExpression, csig : Map[String,Set[HOLConst]], vsig : Map[String, Set[HOLVar]]) :
    (Map[String,Set[HOLConst]], Map[String, Set[HOLVar]]) = e match {
      case v : HOLVar   =>
        val name = v.name
        vsig.get(name) match {
          case Some(list) if list contains v =>
            (csig, vsig)
          case Some(list) =>
            (csig,  vsig + ((name, list+v)) )
          case None =>
            (csig,  vsig + ((name, Set(v))) )
        }

      case c : HOLConst =>
        val name = c.name
        csig.get(name) match {
          case Some(list) if list contains c =>
            (csig, vsig)
          case Some(list) =>
            (csig + ((name, list+c)), vsig )
          case None =>
            (csig + ((name, Set(c))), vsig )
        }

      case HOLApp(s,t) =>
        val (cm1,vm1) = getSignature(s, csig, vsig)
        val (cm2,vm2) = getSignature(t, cm1, vm1)

        val cmtotal = (cm1.toList ++ cm2.toList).foldLeft(Map[String, Set[HOLConst]]())( (map, elem) =>
          map.get(elem._1) match {
            case None => map + elem
            case Some(list) => map + ((elem._1, list ++ elem._2))
          }
        )

        val vmtotal = (vm1.toList ++ vm2.toList).foldLeft(Map[String, Set[HOLVar]]())( (map, elem) =>
          map.get(elem._1) match {
            case None => map + elem
            case Some(list) => map + ((elem._1, list ++ elem._2))
          }

        )

        (cmtotal, vmtotal)

      case HOLAbs(x@HOLVar(name,_), s) =>
        val (cm1,vm1) = getSignature(s, csig, vsig)
        vm1.get(name) match {
          case None =>
            (cm1, vm1 + ((name,Set(x.asInstanceOf[HOLVar]))))
          case Some(list) =>
            (cm1, vm1 + ((name, list + x.asInstanceOf[HOLVar] )))
        }
    }

  }


  class Robinson2RalAndUndoHOL2Fol(sig_vars : Map[String, List[HOLVar]],
                                   sig_consts : Map[String, List[HOLConst]],
                                   cmap : replaceAbstractions.ConstantsMap) extends RobinsonToRal {
    val absmap = Map[String, HOLExpression]() ++ (cmap.toList.map(x => (x._2.toString, x._1)))
    val cache = Map[HOLExpression, HOLExpression]()

    override def convert_formula(e:HOLFormula) : HOLFormula = {
      require(e.isInstanceOf[FOLFormula])
      recreateWithFactory(Robinson2RalAndUndoHOL2Fol.backtranslate(e.asInstanceOf[FOLFormula], sig_vars, sig_consts, absmap)(HOLFactory), HOLFactory).asInstanceOf[HOLFormula]
    }

    override def convert_substitution(s:Substitution) : Substitution = {
      val mapping = s.map.toList.map(x =>
        (
          recreateWithFactory(Robinson2RalAndUndoHOL2Fol.backtranslate(x._1.asInstanceOf[FOLVar], sig_vars, sig_consts, absmap, None)(HOLFactory), HOLFactory).asInstanceOf[HOLVar],
          recreateWithFactory(Robinson2RalAndUndoHOL2Fol.backtranslate(x._2.asInstanceOf[FOLExpression], sig_vars, sig_consts, absmap, None)(HOLFactory), HOLFactory).asInstanceOf[HOLExpression]
          )
      )

      Substitution(mapping)
    }


  }


  "The higher-order tape proof" should {
    "extract a struct from the preprocessed proof" in {
      checkForProverOrSkip
      show("Loading file")
      val tokens = HybridLatexParser.parseFile(tempCopyOfClasspathFile("tape3.llk"))
      val pdb = HybridLatexParser.createLKProof(tokens)
      show("Eliminating definitions, expanding tautological axioms")
      val elp = AtomicExpansion(DefinitionElimination(pdb.Definitions, regularize(pdb.proof("TAPEPROOF"))))
      show("Skolemizing")
      val selp = LKtoLKskc(elp)

      show("Extracting struct")
      val struct = StructCreators.extract(selp, x => containsQuantifier(x) || freeHOVariables(x).nonEmpty)
      show("Computing projections")
      val proj = Projections(selp, x => containsQuantifier(x) || freeHOVariables(x).nonEmpty)

      show("Computing clause set")
      val cl = AlternativeStandardClauseSet(struct)
      show("Exporting to prover 9")
      val (cmap, folcl_) = replaceAbstractions(cl.toList)
      println("Calculated cmap: ")
      cmap.map(x => println(x._1+" := "+x._2))

      val folcl = reduceHolToFol(folcl_)
      folcl.map(println(_))

      show("Refuting clause set")
      Prover9.refute(folcl) match {
        case None =>
          ko("could not refute clause set")
        case Some(rp) =>
          show("Getting formulas")
          val proofformulas = selp.nodes.flatMap(_.asInstanceOf[LKProof].root.toFSequent.formulas  ).toList.distinct

          show("Extracting signature from "+proofformulas.size+ " formulas")
          val (sigc, sigv_) = Robinson2RalAndUndoHOL2Fol.getSignature( proofformulas )

          //adding variables geenrated by prover9 / prooftrans
          val sigv = sigv_ ++ List(("v0", Set(HOLVar("v0", Ti))), ("v1", Set(HOLVar("v1", Ti))))

          show("Converting to Ral")

          val myconverter = Robinson2RalAndUndoHOL2Fol(sigv.map(x => (x._1, x._2.toList)), sigc.map(x => (x._1, x._2.toList)), cmap)
          val ralp = myconverter(rp)
          show("Creating acnf")
          //val acnf = ceres_omega(proj, ralp, sequentToLabelledSequent(selp.root), struct)

          ok
      }

    }
  }

}
