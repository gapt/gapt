package at.logic.gapt.proofs.lk
import at.logic.gapt.expr.{LambdaExpression, _}
import at.logic.gapt.proofs._

import scala.math._

/**
 * The plan is to put all future function, classes, etc. dealing with linkProof schemata into this file.
 * Created by Ermine516 on 02.02.17.
 */

/**
 * The Point of this class is to allow the instantiation of linkProof schemata.
 * We provide two functions, one for linkProof schemata indexed by inductive datatypes
 * and one for linkProof schemata indexed by numeric expressions only.
 */
class LKProofSchemata {

  /**
   * Note that there is no guarantee that instantiated linkProof schemata will result in a finite
   * linkProof, thus one must provide a maxdepth function which takes a sequence of lambda expressions
   * and returns an integer. That is the max depth to unroll the linkProof schemata two.
   * @param ProofName The name of the linkProof
   * @param args The arguements for the free parameters of the linkProof.
   */
  def Instantiate( ProofName: String, args: Seq[LambdaExpression] /*,
                              MaxDepth: ( Seq[LambdaExpression] => Int ) = MaxDepthInit */)( implicit ctx: Context ): Option[LKProof] = {

    val canonicalName = ctx.get[Context.ProofNames].names.get(ProofName)
    val invariants = ctx.get[Context.ProofDefinitions].components.get(ProofName)
    (canonicalName,invariants) match{
      case (Some((Apps(_,cargs),_)),Some(invar)) =>
        if(cargs.size == args.size) invar.fold(None)(
          (found,search) => { if(found == None) search match{
           case (Apps(_, vs), lkp ) => syntacticMatching(vs.zip(args)) match{
               case Some(subs) =>  Some((subs, lkp))
               case None => None }
           case _ => None } else None
          }) match{
             case Some((subs:Substitution,lkp:LKProof)) => buildProof(subs,lkp)(ctx)
             case None => None
        } else None
      case _ => None
    }
    


    def buildProof( subs: Substitution, linkProof: LKProof)( implicit ctx: Context ): Option[LKProof] = linkProof match {

    case  ProofLink( le , _ ) => le match{
      case Apps( at.logic.gapt.expr.Const(c,_), vs) =>
        Instantiate(c,subs(vs))(ctx) match{
          case Some(p) => Some(p)
          case None => None
        }
      case _ => None
    }

    case InitialSequent( _ ) => Some(linkProof)

    case WeakeningLeftRule( subProof, formula ) =>
      buildProof(subs, subProof)(ctx) match{
        case Some(p) => Some(WeakeningLeftRule(p, subs(formula)))
        case None => None
      }
    case WeakeningRightRule( subProof, formula ) =>
      buildProof(subs, subProof)(ctx) match{
        case Some(p) => Some(WeakeningRightRule(p, subs(formula)))
        case None => None
      }
    case ContractionLeftRule( subProof, _, _ ) =>
      buildProof(subs, subProof)(ctx) match{
        case Some(p) => Some(ContractionLeftRule(p, subs(linkProof.mainFormulas.head)))
        case None => None
      }
    case ContractionRightRule( subProof, _, _ ) =>
      buildProof(subs, subProof)(ctx) match{
        case Some(p) => Some(ContractionRightRule(p, subs(linkProof.mainFormulas.head)))
        case None => None
      }
    case AndRightRule( leftSubProof, _, rightSubProof, _ ) =>
      (buildProof(subs, leftSubProof)(ctx),  buildProof(subs,rightSubProof)(ctx)) match{
        case (Some(pl),Some(pr)) => Some(AndRightRule( pl, pr, subs(linkProof.mainFormulas.head) ))
        case _ => None
      }
    case AndLeftRule( subProof, _, _ ) =>
      buildProof(subs, subProof)(ctx) match{
        case Some(p) => Some(AndLeftRule(p, subs(linkProof.mainFormulas.head)))
        case None => None
      }
    case OrLeftRule( leftSubProof, _, rightSubProof, _ ) =>
      (buildProof(subs, leftSubProof)(ctx),  buildProof(subs,rightSubProof)(ctx)) match{
        case (Some(pl),Some(pr)) => Some(OrLeftRule( pl, pr, subs(linkProof.mainFormulas.head) ))
        case _ => None
      }
    case OrRightRule( subProof, _, _ ) =>
      buildProof(subs, subProof)(ctx) match{
        case Some(p) => Some(OrRightRule(p, subs(linkProof.mainFormulas.head)))
        case None => None
      }

    case ImpLeftRule( leftSubProof, _, rightSubProof, _ ) =>
      (buildProof(subs, leftSubProof)(ctx),  buildProof(subs,rightSubProof)(ctx)) match{
        case (Some(pl),Some(pr)) => Some(ImpLeftRule( pl, pr, subs(linkProof.mainFormulas.head) ))
        case _ => None
      }
    case ImpRightRule( subProof, _, _ ) =>
      buildProof(subs, subProof)(ctx) match{
        case Some(p) => Some(ImpRightRule(p, subs(linkProof.mainFormulas.head)))
        case None => None
      }
    case NegLeftRule( subProof, _ ) =>
      buildProof(subs, subProof)(ctx) match{
        case Some(p) => Some(NegLeftRule(p, subs(linkProof.auxFormulas.head.head)))
        case None => None
      }

    case NegRightRule( subProof, _ ) =>
      buildProof(subs, subProof)(ctx) match{
        case Some(p) => Some(NegRightRule(p, subs(linkProof.auxFormulas.head.head)))
        case None => None
      }
    case ForallLeftRule( subProof, _, _, term, _ ) =>
      buildProof(subs, subProof)(ctx) match{
        case Some(p) => Some(ForallLeftRule(p, subs(linkProof.mainFormulas.head), subs(term)))
        case None => None
      }

    case ForallRightRule( subProof, _, eigen, _ ) =>
      buildProof(subs, subProof)(ctx) match{
        case Some(p) => Some(ForallRightRule(p, subs(linkProof.mainFormulas.head), eigen))
        case None => None
      }

    case ExistsLeftRule( subProof, _, eigen, _ ) =>
      buildProof(subs, subProof)(ctx) match{
        case Some(p) => Some(ExistsLeftRule(p, subs(linkProof.mainFormulas.head), eigen))
        case None => None
      }

    case ExistsRightRule( subProof, _, _, term, _ ) =>
      buildProof(subs, subProof)(ctx) match{
        case Some(p) => Some(ExistsRightRule(p, subs(linkProof.mainFormulas.head), subs(term)))
        case None => None
      }

   /*case ForallSkRightRule( subProof, _, _, skTerm, skDef ) =>
    ForallSkRightRule( buildProof( subs, subProof), subs(skTerm), skDef )

    case ExistsSkLeftRule( subProof, _, _, skTerm, skDef ) =>
    ExistsSkLeftRule( buildProof( subs, subProof), subs(skTerm), skDef )*/

    case EqualityLeftRule( subProof, _, _, _ ) =>
      buildProof(subs, subProof)(ctx) match{
        case Some(p) => Some(EqualityLeftRule(p, subs(linkProof.auxFormulas.head.head), subs(linkProof.auxFormulas.head( 1 )), subs(linkProof.mainFormulas.head)))
        case None => None
      }

    case EqualityRightRule( subProof, _, _, _ ) =>
      buildProof(subs, subProof)(ctx) match{
        case Some(p) => Some(EqualityRightRule(p, subs(linkProof.auxFormulas.head.head), subs(linkProof.auxFormulas.head( 1 )), subs(linkProof.mainFormulas.head)))
        case None => None
      }
    case CutRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      (buildProof(subs, leftSubProof)(ctx),  buildProof(subs,rightSubProof)(ctx)) match{
        case (Some(pl),Some(pr)) => Some(CutRule( pl,subs(leftSubProof.endSequent( aux1 )), pr, subs(rightSubProof.endSequent( aux2 )) ))
        case _ => None
      }
  }

      





    //We should require the first numericArgs args to be variable free.
    //if numericArgs is greater than the size of args we have an error
    //if the size of args is greater than the expected number of arges for proofName
    //we have an error

    /*We could assume that the deepest the recursion can go is the maximum term depth of the
      parameter arguements multiplied together. This is a sensible assumption
      Thus, if we exceed this value the s
     */

    None
  }
  /**
   * This is the initial max depth function and just computes the depth of the the indivitual
   * arguments and multiplies them together.
   * @param args The arguements for the free parameters of the linkProof.
   */
  def MaxDepthInit( args: Seq[LambdaExpression] ): Int =
    args.fold( 1 )( ( tot, curLe ) => {
      val one: Int = termDepth( curLe.asInstanceOf[LambdaExpression] ) match {
        case Some( i ) => i
        case None      => -1
      }
      if ( one >= 0 ) tot.asInstanceOf[Int] * one
      else -1
    } ).asInstanceOf[Int]
  /**
   * A helper function for MaxDepthInit
   * @param Term The term to compute the depth of
   */
  def termDepth( Term: LambdaExpression ): Option[Int] = {
    Term match {
      case at.logic.gapt.expr.Const( _, _ ) => Some( 1 )
      case Var( _, _ )                      => Some( 1 )
      case Apps( func, args ) =>
        val two: Int = args.map( term => termDepth( term ) ).fold( 0 )( ( x, y ) => y match {
          case Some( i ) => if ( 0 <= x.asInstanceOf[Int] ) max( x.asInstanceOf[Int], i.asInstanceOf[Int] ) else -1
          case None      => -1
        } ).asInstanceOf[Int]
        val three: Int = termDepth( func ) match {
          case Some( i ) => i
          case None      => -1
        }
        Some( if ( three < 0 ) -1 else three + two )

      case Abs( _, t ) => Some( termDepth( t ) match {
        case Some( i ) => if ( i != -1 ) max( 1, i ) else -1
        case None      => -1
      } )
      case _ => None
    }
  }
}
