import ammonite.ops.{read => _, write => _, _}
import gapt._
import gapt.examples._
import gapt.expr._
import gapt.expr.fol._
import gapt.expr.hol._
import gapt.formats.babel.BabelParser.parseFormula
import gapt.formats.dimacs._
import gapt.formats.tip._
import gapt.formats.tptp._
import gapt.formats.verit._
import gapt.formats.smt._
import gapt.formats.llk._
import gapt.formats.latex._
import gapt.formats.json._
import gapt.formats.implicits._
import gapt.formats.InputFile
import gapt.grammars._
import gapt.proofs.reduction._
import gapt.proofs.rup._
import gapt.proofs.epsilon._
import gapt.proofs.expansion._
import gapt.proofs.hoare._
import gapt.proofs._
import gapt.proofs.context._
import gapt.proofs.context.mutable._
import gapt.proofs.context.immutable._
import gapt.proofs.context.update._
import gapt.proofs.context.facet._
import gapt.proofs.ceres._
import gapt.proofs.lk._
import gapt.cutintro._
import gapt.proofs.resolution._
import gapt.provers.sat._
import gapt.provers.leancop._
import gapt.provers.viper._
import gapt.provers.prover9._
import gapt.provers.maxsat._
import gapt.provers.eprover._
import gapt.provers.iprover._
import gapt.provers.metis._
import gapt.provers.vampire._
import gapt.provers.verit._
import gapt.provers.smtlib._
import gapt.provers.escargot._
import gapt.provers.slakje.Slakje
import gapt.provers.spass._
import gapt.prooftool.prooftool
import gapt.utils._
import cats.syntax.all._, cats.instances.all._, EitherHelpers._
import gapt.cli.GPL.{ apply => copying, printLicense => license }
