import at.logic.gapt.proofs.expansionTrees._
import at.logic.gapt.proofs.lkOld.{LKToExpansionProof, LKProver}
import at.logic.gapt.provers.prover9.Prover9Importer

// list of files without equality reasoning randomly chosen all over prover9-TSTP
val fns = List(
"AGT/AGT004+1/Prover9---1109a.THM-Ref.s.out",
"AGT/AGT017+1/Prover9---1109a.THM-Ref.s.out",
"ALG/ALG002-1/Prover9---1109a.UNS-Ref.s.out",
"ALG/ALG216+1/Prover9---1109a.THM-Ref.s.out",
"ALG/ALG434-1/Prover9---1109a.UNS-Ref.s.out",
"ANA/ANA025-2/Prover9---1109a.UNS-Ref.s.out",
"CAT/CAT005-1/Prover9---1109a.UNS-Ref.s.out",
"COL/COL055-1/Prover9---1109a.UNS-Ref.s.out",
"COL/COL114-1/Prover9---1109a.UNS-Ref.s.out",
"COM/COM003+2/Prover9---1109a.THM-Ref.s.out",
"FLD/FLD009-3/Prover9---1109a.UNS-Ref.s.out",
"FLD/FLD065-3/Prover9---1109a.UNS-Ref.s.out",
"GEO/GEO022-2/Prover9---1109a.UNS-Ref.s.out",
"GEO/GEO047-3/Prover9---1109a.UNS-Ref.s.out",
"GRP/GRP020-1/Prover9---1109a.UNS-Ref.s.out",
"HWV/HWV009-4/Prover9---1109a.UNS-Ref.s.out",
"KRS/KRS070+1/Prover9---1109a.UNS-Ref.s.out",
"MSC/MSC012+1/Prover9---1109a.THM-Ref.s.out",
"NUM/NUM322+1/Prover9---1109a.THM-Ref.s.out",
"NUM/NUM588+3/Prover9---1109a.THM-Ref.s.out",
"PLA/PLA031-1.003/Prover9---1109a.UNS-Ref.s.out",
"PRO/PRO014+2/Prover9---1109a.THM-Ref.s.out",
"KRS/KRS266+1/Prover9---1109a.THM-Ref.s.out",
"LAT/LAT273-2/Prover9---1109a.UNS-Ref.s.out",
"LCL/LCL066-1/Prover9---1109a.UNS-Ref.s.out",
"LCL/LCL216-1/Prover9---1109a.UNS-Ref.s.out",
"MGT/MGT018+1/Prover9---1109a.THM-Ref.s.out",
"PUZ/PUZ018-1/Prover9---1109a.UNS-Ref.s.out",
"RNG/RNG006-1/Prover9---1109a.UNS-Ref.s.out",
"SCT/SCT094-1/Prover9---1109a.UNS-Ref.s.out",
"SET/SET626+3/Prover9---1109a.THM-Ref.s.out",
"SEU/SEU117+1/Prover9---1109a.THM-Ref.s.out",
"SWB/SWB012+2/Prover9---1109a.THM-Ref.s.out",
"SWV/SWV060+1/Prover9---1109a.THM-Ref.s.out",
"TOP/TOP034+1/Prover9---1109a.THM-Ref.s.out"
)

var t_total : Long = 0
val prover = new LKProver

fns.foreach( fn => {
  val p = Prover9Importer.lkProofFromFile( "testing/TSTP/prover9/" + fn )
  val E = LKToExpansionProof( p )
  val F = toDeep( E )

  val t = System.currentTimeMillis
  prover.getLKProof( F )
  val t_this = System.currentTimeMillis - t

  println ( "duration " + fn + ": " + t_this + " ms" )
  t_total += t_this
} )

println( "duration total: " + t_total + " ms" )
