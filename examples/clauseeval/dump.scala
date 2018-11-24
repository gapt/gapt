package gapt.examples

import ammonite.ops._
import gapt.examples.Ty.{ DClause, DClauseSet }
import gapt.expr._
import gapt.expr.arithmetic.int._
import gapt.formats.llk.toLLKString
import gapt.formats.tptp._
import gapt.proofs._
import gapt.utils.NameGenerator

import scala.collection.{ GenTraversable, mutable }
import scala.collection.parallel.ParSeq
import scala.io.Codec

object Memo {
  import gapt.expr

  var ccount = 0
  var vcount = 0
  var appcount = 0
  var abscount = 0

  val consts = mutable.Set[expr.Const]()
  val vars = mutable.Set[expr.Var]()
  val abs = mutable.Set[expr.Abs]()
  val apps = mutable.HashMap[Int, mutable.Set[expr.App]]()

  object Const {
    def apply( name: String, ty: Ty, params: List[Ty] = Nil ) =
      consts.synchronized {
        ccount += 1
        val c = expr.Const( name, ty, params )
        consts find ( u => c == u ) match {
          case Some( x ) => x
          case None =>
            //println( s"consts ${consts.size} / $ccount" )
            consts += c
            c
        }
      }
  }

  object Var {
    def apply( name: String, ty: Ty ) =
      vars.synchronized {
        vcount += 1
        val c = expr.Var( name, ty )
        vars find ( u => c == u ) match {
          case Some( x ) => x
          case None =>
            //println( s"vars ${vars.size} / $vcount" )
            vars += c
            c
        }
      }
  }

  object App {
    def apply( s: expr.Expr, t: expr.Expr ) =
      apps.synchronized {
        appcount += 1
        val c = expr.App( s, t )
        val hash = s.hashCode ^ t.hashCode
        apps.get( hash ) match {
          case Some( set ) =>
            set find ( u => c == u ) match {
              case Some( x ) => x
              case None =>
                //println( s"apps ${apps.size} / $appcount" )
                set += c
                c
            }
          case None =>
            apps( hash ) = mutable.Set( c )
            c
        }
      }
  }

  object Eq {
    def apply( s: expr.Expr, t: expr.Expr ) = {
      require( s.ty == t.ty )
      Memo.App( Memo.App( EqC( s.ty ), s ), t )
    }
  }

  object Abs {
    def apply( s: expr.Var, t: expr.Expr ) =
      abs.synchronized {
        abscount += 1
        val c = expr.Abs( s, t )
        abs find ( u => c == u ) match {
          case Some( x ) => x
          case None =>
            println( s"abs ${abs.size} / $abscount" )
            abs += c
            c
        }
      }
  }

  object Expr {
    def apply( e: expr.Expr ): Expr = e match {
      case expr.Var( name, ty )           => Var( name, ty )
      case expr.Const( name, ty, params ) => Const( name, ty, params )
      case expr.App( s, t )               => App( s, t )
      case expr.Abs( v, t )               => Abs( v, t )
    }
  }
}

object ReadFilenames {
  def apply( fp: Path ) = {
    read.lines( fp, Codec.UTF8 )
  }
  val my_path = "/opt/smtlib/Main Track no BV or QF/dump/stripped/UFLIA/"
  val my_list = "list.txt"
}

object Ty {
  type DClause = Set[Expr]
  type DClauseSet = Set[DClause]
}

case class DumpData[T]( path: String, file_list: String, simplifier: Simplifier[T] ) {
  import Ty.DClause

  val files = ReadFilenames( Path( path + file_list ) )

  //val files = List( "addelementtofile-19.smt2.termdump.tff", "addelementtologfile-7.smt2.termdump.tff", "addelementtologfilewithtruncatechecks-3.smt2.termdump.tff", "addelementtonextfile-1.smt2.termdump.tff", "AdditiveMethods_OwnedResults.F1.smt2.termdump.tff", "adminop-1.smt2.termdump.tff", "AdvancedTypes_AdvancedTypes.Advanced1_SubLessType-orderStrength_1.smt2.termdump.tff", "AdvancedTypes_SubLessType..ctor-orderStrength_1.smt2.termdump.tff", "archivelog-17.smt2.termdump.tff", "archivelog-1.smt2.termdump.tff", "archivelog-20.smt2.termdump.tff", "Array2_test3.MyClass2..ctor.smt2.termdump.tff", "Arrays_P0-noinfer.smt2.termdump.tff", "Array_test3.MyClass.Allocate1_System.Int32.smt2.termdump.tff", "Array_test3.MyClass..ctor.smt2.termdump.tff", "Array_test3.MyClass.M0_test3.MyClass.array_notnull.smt2.termdump.tff", "AssignToNonInvariantField_AnotherClient.P_Bad.smt2.termdump.tff", "AssignToNonInvariantField_ClientClass.GoodUpdateOfY.smt2.termdump.tff", "AssumeEnsures_Proc-noinfer.smt2.termdump.tff", "BasicMethodology_C.foo.smt2.termdump.tff", "BoxedInt_BoxedInt.R_System.Int32.smt2.termdump.tff", "Capture_Capture.Caller2_System.Object_notnull.smt2.termdump.tff", "Cast_Cast..ctor.smt2.termdump.tff", "cat.smt2.termdump.tff", "checkauthcert-2.smt2.termdump.tff", "checkauthcert-3.smt2.termdump.tff", "checkiandacert-12.smt2.termdump.tff", "checkiandacert-13.smt2.termdump.tff", "checkiandacert-8.smt2.termdump.tff", "checkidcertok-11.smt2.termdump.tff", "checkidcertok-8.smt2.termdump.tff", "checkprivcert-15.smt2.termdump.tff", "Chunker7_Chunker..cctor.smt2.termdump.tff", "combinelines-25.smt2.termdump.tff", "completefailedadminlogon-3.smt2.termdump.tff", "completefailedenrolment-2.smt2.termdump.tff", "ConstructorVisibility_Visitor..ctor.smt2.termdump.tff", "ConstructorVisibility_Visitor.VisitLiteral_Literal_notnull.smt2.termdump.tff", "copy_postcondition_of_copy_52_4.smt2.termdump.tff", "delete-1.smt2.termdump.tff", "difference_precondition_of_difference_35_21.smt2.termdump.tff", "digest-169.smt2.termdump.tff", "digest-23.smt2.termdump.tff", "digest-44.smt2.termdump.tff", "digest-49.smt2.termdump.tff", "digest-64.smt2.termdump.tff", "dofind-26.smt2.termdump.tff", "dofind-33.smt2.termdump.tff", "dofind-34.smt2.termdump.tff", "dofind-37.smt2.termdump.tff", "dofind-50.smt2.termdump.tff", "dofind-59.smt2.termdump.tff", "dofind-7.smt2.termdump.tff", "DynamicTypes_Sub0..ctor.smt2.termdump.tff", "Ensures_Q-noinfer.smt2.termdump.tff", "ExposeVersion_QClient.bar-level_2.smt2.termdump.tff", "ExposeVersion_X.FieldUpdateByObjectCreationWithMethodQuery_X_notnull-level_2.smt2.termdump.tff", "extract-6.smt2.termdump.tff", "Finally_ReturnFinally.Expose3_System.Boolean_System.Int32-modifiesOnLoop.smt2.termdump.tff", "Generic_Test.Main.smt2.termdump.tff", "init-11.smt2.termdump.tff", "init-16.smt2.termdump.tff", "init-43.smt2.termdump.tff", "init-6.smt2.termdump.tff", "init-7.smt2.termdump.tff", "insertion_sort_invariant_37_2.smt2.termdump.tff", "insert_postcondition_of_insert_49_4.smt2.termdump.tff", "javafe.ast.ArrayInit.008.smt2.termdump.tff", "javafe.ast.ArrayInit.010.smt2.termdump.tff", "javafe.ast.ArrayType.47.smt2.termdump.tff", "javafe.ast.ASTDecoration.23.smt2.termdump.tff", "javafe.ast.BlockStmt.009.smt2.termdump.tff", "javafe.ast.CatchClause.009.smt2.termdump.tff", "javafe.ast.ClassDecl.75.smt2.termdump.tff", "javafe.ast.ClassDeclStmt.009.smt2.termdump.tff", "javafe.ast.CompoundName.95.smt2.termdump.tff", "javafe.ast.ConstructorDecl.009.smt2.termdump.tff", "javafe.ast.DefaultVisitor.001.smt2.termdump.tff", "javafe.ast.DefaultVisitor.011.smt2.termdump.tff", "javafe.ast.DefaultVisitor.047.smt2.termdump.tff", "javafe.ast.DefaultVisitor.048.smt2.termdump.tff", "javafe.ast.DoStmt.007.smt2.termdump.tff", "javafe.ast.ExprObjectDesignator.006.smt2.termdump.tff", "javafe.ast.ExprVec.004.smt2.termdump.tff", "javafe.ast.FieldAccess.008.smt2.termdump.tff", "javafe.ast.FieldDecl.012.smt2.termdump.tff", "javafe.ast.Identifier.172.smt2.termdump.tff", "javafe.ast.IdentifierVec.016.smt2.termdump.tff", "javafe.ast.ImportDeclVec.019.smt2.termdump.tff", "javafe.ast.InitBlock.002.smt2.termdump.tff", "javafe.ast.InitBlock.198.smt2.termdump.tff", "javafe.ast.LabelStmt.012.smt2.termdump.tff", "javafe.ast.LexicalPragma.001.smt2.termdump.tff", "javafe.ast.LiteralExpr.005.smt2.termdump.tff", "javafe.ast.LocalVarDecl.009.smt2.termdump.tff", "javafe.ast.LocalVarDecl.234.smt2.termdump.tff", "javafe.ast.Name.004.smt2.termdump.tff", "javafe.ast.PrimitiveType.291.smt2.termdump.tff", "javafe.ast.RoutineDecl.004.smt2.termdump.tff", "javafe.ast.SimpleName.017.smt2.termdump.tff", "javafe.ast.SingleTypeImportDecl.002.smt2.termdump.tff", "javafe.ast.SingleTypeImportDecl.005.smt2.termdump.tff", "javafe.ast._SpecialParserInterface.001.smt2.termdump.tff", "javafe.ast.StandardPrettyPrint.323.smt2.termdump.tff", "javafe.ast.SuperObjectDesignator.009.smt2.termdump.tff", "javafe.ast.SwitchStmt.343.smt2.termdump.tff", "javafe.ast.TypeName.003.smt2.termdump.tff", "javafe.ast.TypeName.009.smt2.termdump.tff", "javafe.ast.UnaryExpr.008.smt2.termdump.tff", "javafe.ast.UnaryExpr.423.smt2.termdump.tff", "javafe.ast.VarInitVec.017.smt2.termdump.tff", "javafe.ast.Visitor.002.smt2.termdump.tff", "javafe.ast.VisitorArgResult.051.smt2.termdump.tff", "javafe.filespace.Extension.004.smt2.termdump.tff", "javafe.filespace.Resolve.003.smt2.termdump.tff", "javafe.filespace.Resolve.490.smt2.termdump.tff", "javafe.filespace.Resolve_Result.001.smt2.termdump.tff", "javafe.filespace.SlowQuery.496.smt2.termdump.tff", "javafe.filespace.ZipTree.001.smt2.termdump.tff", "javafe.parser.Lex.016.smt2.termdump.tff", "javafe.parser.test.TestLex.001.smt2.termdump.tff", "javafe.parser.test.TestParse.581.smt2.termdump.tff", "javafe.parser.Token.572.smt2.termdump.tff", "javafe.parser.TokenQueue.008.smt2.termdump.tff", "javafe.reader.CachedReader.005.smt2.termdump.tff", "javafe.reader.MethodSignature.612.smt2.termdump.tff", "javafe.reader.StandardTypeReader.007.smt2.termdump.tff", "javafe.reader.StandardTypeReader.627.smt2.termdump.tff", "javafe.tc.ConstantExpr.001.smt2.termdump.tff", "javafe.tc.ConstantExpr.011.smt2.termdump.tff", "javafe.tc.EnvForCU.653.smt2.termdump.tff", "javafe.tc.EnvForLocalType.005.smt2.termdump.tff", "javafe.tc.FieldDeclVec.017.smt2.termdump.tff", "javafe.tc.FieldDeclVec.020.smt2.termdump.tff", "javafe.tc.FlowInsensitiveChecks.034.smt2.termdump.tff", "javafe.tc.MethodDeclVec.698.smt2.termdump.tff", "javafe.tc.OutsideEnv.002.smt2.termdump.tff", "javafe.tc.OutsideEnv.010.smt2.termdump.tff", "javafe.tc.PrepTypeDeclaration.018.smt2.termdump.tff", "javafe.tc.PrepTypeDeclaration.708.smt2.termdump.tff", "javafe.tc.TypeCheck.003.smt2.termdump.tff", "javafe.tc.TypeCheck.009.smt2.termdump.tff", "javafe.tc.Types.032.smt2.termdump.tff", "javafe.tc.Types.751.smt2.termdump.tff", "javafe.tc.TypeSig.723.smt2.termdump.tff", "javafe.test.Print.761.smt2.termdump.tff", "javafe.util.AssertionFailureException.002.smt2.termdump.tff", "javafe.util.BufferedCorrelatedReader.006.smt2.termdump.tff", "javafe.util.LocationManagerCorrelatedReader.801.smt2.termdump.tff", "javafe.util.Set.806.smt2.termdump.tff", "javafe.util.StackVector.827.smt2.termdump.tff", "javafe.util.SubCorrelatedReader.829.smt2.termdump.tff", "keymatchingissuer-2.smt2.termdump.tff", "list4.smt2.termdump.tff", "list6.smt2.termdump.tff", "LocalExpose_S.V1.smt2.termdump.tff", "LockIncorrect_LockingExample.smt2.termdump.tff", "merge_postcondition_of_merge_34_4.smt2.termdump.tff", "opisavailable-4.smt2.termdump.tff", "overridedoorlockop-2.smt2.termdump.tff", "overridedoorlockop-5.smt2.termdump.tff", "PeerConsistentLoop_Coll.P.smt2.termdump.tff", "poll-2.smt2.termdump.tff", "PureAxioms_B.Dummy2-level_2.smt2.termdump.tff", "putnextserialnumber-2.smt2.termdump.tff", "quicksort_check_heap_access_55_4.smt2.termdump.tff", "quicksort_postcondition_of_quicksort_55_45.smt2.termdump.tff", "readalarmsilent-3.smt2.termdump.tff", "readandcheck-1.smt2.termdump.tff", "readandcheck-3.smt2.termdump.tff", "readandcheck-4.smt2.termdump.tff", "readandcheckauthcert-2.smt2.termdump.tff", "readfar-6.smt2.termdump.tff", "readworkinghours-12.smt2.termdump.tff", "Recursion0_Recursion0.SomeIterations_System.Int32-infer_i.smt2.termdump.tff", "resetscreenmessage-1.smt2.termdump.tff", "Search_Search.ContainsZero_IncMethod_System.Int32.array_notnull-noinfer.smt2.termdump.tff", "SiblingConstructors_SiblingConstructors.SpecSharp.CheckInvariant_System.Boolean.smt2.termdump.tff", "SimpleWhile0_SimpleWhile0.CC77-infer_i.smt2.termdump.tff", "sls_dispose_loop_check_free_26_4.smt2.termdump.tff", "sls_dispose_loop_invariant_27_3.smt2.termdump.tff", "sls_traverse_loop_check_heap_access_31_4.smt2.termdump.tff", "smtlib.1009700.smt2.termdump.tff", "smtlib.1016320.smt2.termdump.tff", "smtlib.1021911.smt2.termdump.tff", "smtlib.1024492.smt2.termdump.tff", "smtlib.1039308.smt2.termdump.tff", "smtlib.1058836.smt2.termdump.tff", "smtlib.1082721.smt2.termdump.tff", "smtlib.1085066.smt2.termdump.tff", "smtlib.1147111.smt2.termdump.tff", "smtlib.1153712.smt2.termdump.tff", "smtlib.1181599.smt2.termdump.tff", "smtlib.1191313.smt2.termdump.tff", "smtlib.1199505.smt2.termdump.tff", "smtlib.1201823.smt2.termdump.tff", "smtlib.1204967.smt2.termdump.tff", "smtlib.1208595.smt2.termdump.tff", "smtlib.1225564.smt2.termdump.tff", "smtlib.1237579.smt2.termdump.tff", "smtlib.1240728.smt2.termdump.tff", "smtlib.1256764.smt2.termdump.tff", "smtlib.1258490.smt2.termdump.tff", "smtlib.1269992.smt2.termdump.tff", "smtlib.1290234.smt2.termdump.tff", "smtlib.1296725.smt2.termdump.tff", "smtlib.1304032.smt2.termdump.tff", "smtlib.1323225.smt2.termdump.tff", "smtlib.1348003.smt2.termdump.tff", "smtlib.1385099.smt2.termdump.tff", "smtlib.1395632.smt2.termdump.tff", "smtlib.1405357.smt2.termdump.tff", "smtlib.1411779.smt2.termdump.tff", "smtlib.1419033.smt2.termdump.tff", "smtlib.1489164.smt2.termdump.tff", "smtlib.1500270.smt2.termdump.tff", "smtlib.567585.smt2.termdump.tff", "smtlib.580173.smt2.termdump.tff", "smtlib.587198.smt2.termdump.tff", "smtlib.590927.smt2.termdump.tff", "smtlib.597780.smt2.termdump.tff", "smtlib.602931.smt2.termdump.tff", "smtlib.604320.smt2.termdump.tff", "smtlib.605153.smt2.termdump.tff", "smtlib.607317.smt2.termdump.tff", "smtlib.609960.smt2.termdump.tff", "smtlib.616234.smt2.termdump.tff", "smtlib.622812.smt2.termdump.tff", "smtlib.630573.smt2.termdump.tff", "smtlib.639340.smt2.termdump.tff", "smtlib.642950.smt2.termdump.tff", "smtlib.647792.smt2.termdump.tff", "smtlib.649682.smt2.termdump.tff", "smtlib.651574.smt2.termdump.tff", "smtlib.654035.smt2.termdump.tff", "smtlib.660166.smt2.termdump.tff", "smtlib.660764.smt2.termdump.tff", "smtlib.662008.smt2.termdump.tff", "smtlib.664179.smt2.termdump.tff", "smtlib.669024.smt2.termdump.tff", "smtlib.670736.smt2.termdump.tff", "smtlib.675415.smt2.termdump.tff", "smtlib.684085.smt2.termdump.tff", "smtlib.693289.smt2.termdump.tff", "smtlib.702638.smt2.termdump.tff", "smtlib.706087.smt2.termdump.tff", "smtlib.724613.smt2.termdump.tff", "smtlib.725125.smt2.termdump.tff", "smtlib.726426.smt2.termdump.tff", "smtlib.731945.smt2.termdump.tff", "smtlib.734008.smt2.termdump.tff", "smtlib.734913.smt2.termdump.tff", "smtlib.737188.smt2.termdump.tff", "smtlib.748168.smt2.termdump.tff", "smtlib.748520.smt2.termdump.tff", "smtlib.750680.smt2.termdump.tff", "smtlib.750972.smt2.termdump.tff", "smtlib.757645.smt2.termdump.tff", "smtlib.764308.smt2.termdump.tff", "smtlib.773316.smt2.termdump.tff", "smtlib.779579.smt2.termdump.tff", "smtlib.780689.smt2.termdump.tff", "smtlib.780731.smt2.termdump.tff", "smtlib.781204.smt2.termdump.tff", "smtlib.790200.smt2.termdump.tff", "smtlib.802302.smt2.termdump.tff", "smtlib.802328.smt2.termdump.tff", "smtlib.804621.smt2.termdump.tff", "smtlib.812524.smt2.termdump.tff", "smtlib.821400.smt2.termdump.tff", "smtlib.822869.smt2.termdump.tff", "smtlib.828261.smt2.termdump.tff", "smtlib.835056.smt2.termdump.tff", "smtlib.837615.smt2.termdump.tff", "smtlib.839268.smt2.termdump.tff", "smtlib.840895.smt2.termdump.tff", "smtlib.842199.smt2.termdump.tff", "smtlib.844322.smt2.termdump.tff", "smtlib.849630.smt2.termdump.tff", "smtlib.853704.smt2.termdump.tff", "smtlib.856706.smt2.termdump.tff", "smtlib.866894.smt2.termdump.tff", "smtlib.873453.smt2.termdump.tff", "smtlib.881201.smt2.termdump.tff", "smtlib.894034.smt2.termdump.tff", "smtlib.897372.smt2.termdump.tff", "smtlib.899211.smt2.termdump.tff", "smtlib.900926.smt2.termdump.tff", "smtlib.901684.smt2.termdump.tff", "smtlib.905755.smt2.termdump.tff", "smtlib.914026.smt2.termdump.tff", "smtlib.928305.smt2.termdump.tff", "smtlib.940628.smt2.termdump.tff", "smtlib.942776.smt2.termdump.tff", "smtlib.959440.smt2.termdump.tff", "smtlib.967139.smt2.termdump.tff", "smtlib.967752.smt2.termdump.tff", "startadminactivity-2.smt2.termdump.tff", "startadminactivity-4.smt2.termdump.tff", "startentry-1.smt2.termdump.tff", "StaticFields_StaticFields.M.smt2.termdump.tff", "StrictReadOnly_C2.X1.smt2.termdump.tff", "Strings_test3.MyStrings.SpecSharp.CheckInvariant_System.Boolean.smt2.termdump.tff", "Strings_test3.MyStrings.UnpackString_System.String_notnull.smt2.termdump.tff", "StructTests_St.S_System.Int32.ptr_System.Int32.ptr-level_2.smt2.termdump.tff", "thedisplayfields-13.smt2.termdump.tff", "tohtml.Java2Html.033.smt2.termdump.tff", "unlockdoor-8.smt2.termdump.tff", "updatedooralarm-1.smt2.termdump.tff", "updatedooralarm-8.smt2.termdump.tff", "updateendtimefromfile-2.smt2.termdump.tff", "updateinternallatch-12.smt2.termdump.tff", "updatescreen-1.smt2.termdump.tff", "ValidAndPrevalid_Interval.Foo6.smt2.termdump.tff", "validateandaddkey-16.smt2.termdump.tff", "validateandaddkey-4.smt2.termdump.tff", "validatefinger-18.smt2.termdump.tff", "validateusertoken-4.smt2.termdump.tff", "validateusertoken-5.smt2.termdump.tff", "validateusertoken-8.smt2.termdump.tff", "VisibilityBasedInvariants_Friend..ctor_Thing_notnull.smt2.termdump.tff", "VisibilityBasedInvariants_Friend..ctor_Thing_notnull_System.Boolean.smt2.termdump.tff", "visitTryCatchStmt.smt2.termdump.tff", "WC-EI1_RTE.ExecuteInstruction-vc_nested.smt2.termdump.tff", "WhereMotivation_Types.MLoop0-modifiesOnLoop_1.smt2.termdump.tff", "workinghourstext-4.smt2.termdump.tff", "writefile-14.smt2.termdump.tff", "writefile-15.smt2.termdump.tff", "writefile-20.smt2.termdump.tff", "writefile-40.smt2.termdump.tff", "z3.572385.smt2.termdump.tff", "z3.676467.smt2.termdump.tff", "z3.855423.smt2.termdump.tff" )
  //val path = "/opt/smtlib/Main Track no BV or QF/dumptest/stripped/"
  //  val files = Dumpfiles.files
  //  val path = Dumpfiles.path

  def parse[R]( fun: FilePath => GenTraversable[R] ): ParSeq[R] =
    files.map( x => FilePath( path + x ) ).par.flatMap( ( x: FilePath ) => fun( x ) )

  def getClauses( x: FilePath ) =
    try {
      val cl_pairs: Seq[( DClause, DClause )] =
        tptpInferTypes( TptpParser.load( x ) ).inputs.collect {
          case a @ AnnotatedFormula( _, _, _, f, _ ) =>
            val cl = toCSet( f ).map( Memo.Expr( _ ) )
            val simple = simplifier.simplifyC( cl, simplifier.defaultCache() )
            ( cl, simple )
        }
      val r = ( x, cl_pairs.toSet )
      print( "." )
      Some( r )
    } catch {
      case _: Exception =>
        print( "x" )
        None
    }

  def normalize( f: Formula ) = {
    val fv = freeVariables( f )
    val mapping = fv.zip( Range( 1, fv.size ) ).map { case ( v, i ) => ( v, Var( "X" + i, v.ty ) ) }
    Substitution( mapping )( f )
  }

  def toCSet( formula: Formula ): DClause = {
    ( normalize( formula ) match {
      case All.Block( _, Or.nAry( ls ) ) => ls
    } ).toSet
  }

  def toSequent( formula: Formula ) = {
    val ( neg, pos ) = ( formula match {
      case All.Block( _, Or.nAry( ls ) ) => ls
    } ).partition( { case Neg( _ ) => true; case _ => false } )
    Sequent( neg.map( { case Neg( x ) => x } ), pos )
  }

  def isTautologyC( cl: Set[Formula] ) = cl.exists( x => cl.exists( y => x == Neg( y ) ) )

  lazy val seqs = parse( getClauses ).toSet.par.flatMap( ( x: ( FilePath, Set[( DClause, DClause )] ) ) => x._2 ).seq

}

trait Simplifier[T] {
  import Ty.DClause
  def defaultCache(): T

  def simplify( e: Expr, cache: T ): Expr

  def isInterpreted( s: String ) = tptpInferTypes.isNumeral( s ) || ( Set( "$sum", "$product", "$uminus", "$difference",
    "$less", "$lesseq", "$greater", "$greatereq" ) contains s )

  def simplifyT( ty: Ty ): Ty = ty match {
    case Ti        => Ti
    case To        => To
    case TInt      => TInt
    case t1 ->: t2 => simplifyT( t1 ) ->: simplifyT( t2 )
    case _         => Ti
  }
  def simplifyC( inset: Set[Expr], cache: T ): DClause = {
    val set = mutable.Set[Expr]()
    for ( exp <- inset ) {
      val simple = simplify( exp, cache )
      set += simple
    }
    set.toSet
  }

  def stringOfCache( c: T ): String;

}

object Caches {
  type C1 = ( mutable.Map[Ty, Const], mutable.Map[Ty, Var], NameGenerator )
  type C2 = ( mutable.Map[Ty, Const], mutable.Map[Ty, Var], mutable.Map[Const, Const], NameGenerator )
}

object AggressiveSimplifier extends Simplifier[Caches.C1] {
  def defaultCache(): Caches.C1 =
    ( mutable.Map[Ty, Const](), mutable.Map[Ty, Var](), new NameGenerator( Nil ) )

  def stringOfCache( c: Caches.C1 ) = s"${c._1.size}-${c._2.size}"

  def simplify( e: Expr, cache: Caches.C1 ): Expr = {
    val ( cmap, vmap, ng ) = cache
    e match {
      case NonLogicalConstant( _, ty, _ ) if cmap.contains( ty ) =>
        cmap( ty )
      case NonLogicalConstant( name, ty, _ ) =>
        val base = ( isInterpreted( name ), arity( ty ) ) match {
          case ( true, 0 )  => "cint"
          case ( true, _ )  => "fint"
          case ( false, 0 ) => "c"
          case ( false, _ ) => "f"
        }
        val nc = Memo.Const( ng.fresh( base ), simplifyT( ty ) )
        cmap += ( ( ty, nc ) )
        nc
      case c @ Const( _, _, _ ) => //logical constants
        c

      case Var( _, ty ) if vmap.contains( ty ) =>
        vmap( ty )
      case v @ Var( name, ty ) =>
        /*
        val base = ( isInterpreted( name ), arity( ty ) ) match {
          case ( _, 0 ) => "X"
          case ( _, _ ) => "Fun"
        } */
        val nv = Memo.Var( name, simplifyT( ty ) )
        vmap += ( ( ty, nv ) )
        nv
      case Eq( s, t ) => //equality might have changed type
        val s0 = simplify( s, cache )
        val t0 = simplify( t, cache )
        Memo.Eq( s0, t0 )
      case App( s, t ) =>
        val s0 = simplify( s, cache )
        val t0 = simplify( t, cache )
        Memo.App( s0, t0 )
      case Abs( s, t ) =>
        val s0 @ Var( _, _ ) = simplify( s, cache )
        val t0 = simplify( t, cache )
        Memo.Abs( s0, t0 )
    }
  }

}

object UninterpretedSimplifier extends Simplifier[Caches.C2] {
  def defaultCache() =
    ( mutable.Map[Ty, Const](), mutable.Map[Ty, Var](), mutable.Map[Const, Const](), new NameGenerator( Nil ) )

  def stringOfCache( c: Caches.C2 ) = s"${c._1.size}-${c._2.size}-${c._3.size}"

  val posnum = Memo.Const( "posN", TInt )
  val negnum = Memo.Const( "negN", TInt )
  val num = Memo.Const( "num", TInt )

  def simplify( e: Expr, cache: Caches.C2 ): Expr = {
    val ( cmap, vmap, iconsts, ng ) = cache

    e match {
      case c @ NonLogicalConstant( name, ty, _ ) if iconsts.contains( c ) =>
        iconsts( c )
      case NonLogicalConstant( name, ty, _ ) if cmap.contains( ty ) && !isInterpreted( name ) =>
        cmap( ty )
      case NonLogicalConstant( name, TInt, _ ) if tptpInferTypes.isNumeral( name ) =>
        num
      case NonLogicalConstant( name, ty, _ ) if isInterpreted( name ) =>
        val nc = Const( name, simplifyT( ty ) )
        cmap += ( ( ty, nc ) )
        nc
      case c @ NonLogicalConstant( name, ty, _ ) =>
        val base = arity( ty ) match {
          case 0 => "c"
          case _ => "f"
        }
        val nc = Memo.Const( ng.fresh( base ), simplifyT( ty ) )
        iconsts += ( ( c, nc ) )
        nc
      case c @ Const( _, _, _ ) => //logical constants
        c
      case Var( _, ty ) if vmap.contains( ty ) =>
        vmap( ty )
      case v @ Var( name, ty ) =>
        val nv = Memo.Var( name, simplifyT( ty ) )
        vmap += ( ( ty, nv ) )
        nv
      case Eq( s, t ) => //equality might have changed type
        val s0 = simplify( s, cache )
        val t0 = simplify( t, cache )
        Memo.Eq( s0, t0 )
      case App( s, t ) =>
        val s0 = simplify( s, cache )
        val t0 = simplify( t, cache )
        Memo.App( s0, t0 )
      case Abs( s, t ) =>
        val s0 @ Var( _, _ ) = simplify( s, cache )
        val t0 = simplify( t, cache )
        Memo.Abs( s0, t0 )
    }
  }

}

case class Dump[T]( data: DumpData[T], simp: Simplifier[T] ) {
  def fmt( cl: Set[Expr] ) = cl.map( toLLKString( _ ) ).mkString( " ; " )

  lazy val pairmap = {
    val map = mutable.Map[Set[Expr], mutable.Set[Set[Expr]]]()
    val cache = simp.defaultCache()
    for ( ( cl, nf ) <- data.seqs ) {
      add( nf, cl, map )
    }
    print( "done" )
    map
  }

  def inc[T]( v: T, m: mutable.Map[T, Int] ) = {
    val count = m.getOrElse( v, 0 ) + 1
    m( v ) = count
    ()
  }

  def add[T, U]( k: T, v: U, m: mutable.Map[T, mutable.Set[U]] ) = {
    if ( m contains k ) {
      m( k ) += v
    } else {
      m( k ) = mutable.Set( v )
    }
    ()
  }

  lazy val nfs = data.seqs.map( _._2 )

  lazy val countermap = {
    val map = mutable.Map[Set[Expr], Int]()
    val cache = simp.defaultCache
    for ( ( _, nf ) <- data.seqs ) {
      inc( nf, map )
    }
    map
  }

  def find( values: Set[Set[Expr]] ) = {
    val map = mutable.Map[DClause, mutable.Set[DClause]]()
    for ( ( cl, nf ) <- data.seqs ) {
      if ( values contains nf )
        add( nf, cl, map )
    }
    map
  }

  def printNFs() = {
    for ( ( cl, nf ) <- data.seqs ) {
      print( nf.mkString( " ∨ " ) )
    }
  }

  lazy val top30 = pairmap.filter( _._2.size > 100 ).toList.sortBy( _._2.size ).reverse.take( 30 )
  def printTop30() = top30.map( x => println( s"* (${x._2.size}) ${x._1.mkString( " ; " )}" ) )

}

