package at.logic.algorithms.fol.hol2fol

import at.logic.algorithms.fol.recreateWithFactory
import at.logic.language.fol.{FOLExpression, FOLFormula}
import at.logic.language.hol._
import at.logic.language.lambda.FactoryA
import at.logic.language.lambda.symbols.StringSymbol
import at.logic.language.lambda.types.{Ti, TA, To}
import at.logic.utils.logging.Logger
import org.slf4j.LoggerFactory


/**
 * This is implements some heuristics to convert a fol formula obtained by
 * [[replaceAbstractions]] and [[reduceHolToFol]] back to its original signature.
 * Sometimes, types have to be guessed and the code is poorly tested, so it is unclear
 * how general it is. It works (and is necessary) during the acnf creation of the n-tape proof.
 *
 * To extract a signature, use the [[undoHol2Fol.getSignature]], to to the back translation use
 * [[undoHol2Fol.backtranslate]].
 */
object undoHol2Fol extends Logger {
  override def loggerName = "HOL2FOLLogger"

  /**
   * Translate the fol formula e to a hol formula over the given signature for constants and variables.
   * @param e the fol formula.
   * @param sig_vars a mapping fol name to hol var with appropriate type
   * @param sig_consts a mapping fol name to hol const with appropriate type
   * @param abssymbol_map a mapping fol constant name to a lambda expression (obtained by replaceAbstractions)
   * @param factory the factory used for the return formula
   * @return the changed formula
   */
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
        val qterm_ = recreateWithFactory(abssymbol_map(name), factory).asInstanceOf[HOLExpression] //unsafe cast
        val qterm : HOLExpression = freeVariables(qterm_).foldRight(qterm_)((v,term) => HOLAbs(v,term))
        expected_type match {
          case Some(expt) =>
            require(qterm.exptype == expt, "We did a replacement of the symbol "+name+" by "+qterm+" but the type "+qterm.exptype+" is not the expected type "+expected_type)
            qterm
          case None =>
            qterm
        }

      case Function(HOLConst(name, _), args, _) if abssymbol_map.contains(name) =>
        val qterm_ = recreateWithFactory(abssymbol_map(name), factory).asInstanceOf[HOLExpression] //unsafe cast
        val qterm : HOLExpression = freeVariables(qterm_).foldRight(qterm_)((v,term) => HOLAbs(v,term))
        val btargs = args.map(x => backtranslate(x.asInstanceOf[FOLExpression],sig_vars, sig_consts, abssymbol_map, None)(factory))
        val r = btargs.foldLeft(qterm)((term, nextarg) => HOLApp(term, nextarg))
        expected_type match {
          case Some(expt) =>
            require(qterm.exptype == expt, "We did a replacement of the symbol "+name+" by "+qterm+" but the type "+qterm.exptype+" is not the expected type "+expected_type)
            r
          case None =>
            r
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
        trace("Guessing that the variable "+name+" comes from ivy, assigning type i.")
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
