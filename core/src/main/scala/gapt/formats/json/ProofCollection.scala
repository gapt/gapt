package gapt.formats.json

import cats.data.StateT
import gapt.proofs.DagProof
import io.circe.Decoder.Result
import io.circe._
import io.circe.KeyEncoder._
import cats.implicits._
import cats.data.StateT._

/**
 * Wraps a map from proofs to integers. Each proof must be mapped to a
 * higher number than its subproofs.
 */
class ProofCollection[P <: DagProof[P]] private ( val proofMap: Map[P, Int] ) extends AnyVal

object ProofCollection {
  /**
   * Creates a [[ProofCollection]] from a proof by
   * enumerating all its subproofs in post order, disregarding duplicates.
   */
  def apply[P <: DagProof[P]]( p: P ): ProofCollection[P] = ProofCollection( p.dagLike.postOrder.zipWithIndex.toMap )

  /**
   * Creates a [[ProofCollection]] from a map. Each proof
   * must be mapped to a higher number than its subproofs.
   */
  def apply[P <: DagProof[P]]( m: Map[P, Int] ): ProofCollection[P] = {
    require( m.forall {
      case ( p, i ) =>
        p.immediateSubProofs.forall( q => m.contains( q ) && m( q ) < i )
    } )

    new ProofCollection( m )
  }
}

/**
 * Serializes a collection of proofs.
 * The resulting JSON structure is an object with keys in ℕ and
 * proofs as values. Each of the proofs is serialized by the encodeProof function.
 * @param encodeProof An encoder for Proofs relative to the collection.
 */
class ProofCollectionEncoder[P <: DagProof[P]]( encodeProof: Map[P, Int] => Encoder[P] ) extends Encoder[ProofCollection[P]] {
  override def apply( coll: ProofCollection[P] ): Json =
    Encoder.encodeMap[Int, P]( implicitly, encodeProof( coll.proofMap ) )( coll.proofMap.toList.map( _.swap ).toMap )
}

/**
 * Deserializes a collection of proofs.
 * The expected format is an object with keys in ℕ and proofs as values,
 * where each subproof is referenced by a number.
 * @param decodeProof A decoder for individual proofs relative to a map.
 */
class ProofCollectionDecoder[P <: DagProof[P]]( decodeProof: Map[Int, P] => Decoder[P] ) extends Decoder[ProofCollection[P]] {
  type S = Map[Int, P]
  type M[T] = StateT[Decoder.Result, S, T]

  /**
   * Decodes a single proof by looking up its subproofs in a map,
   * then adds it to the map with the next index.
   */
  private def readProof( j: Json ): M[Unit] = for {
    m <- get[Decoder.Result, S]
    i = m.size
    p <- liftF( decodeProof( m ).decodeJson( j ) )
    _ <- set[Decoder.Result, S]( m + ( ( i, p ) ) )
  } yield ()

  def apply( c: HCursor ): Result[ProofCollection[P]] = for {
    l <- Decoder.decodeMap[Int, Json]( implicitly, implicitly )( c )
    m <- l.toList.sortBy( _._1 ).map( _._2 ).traverse[M, Unit]( readProof ).runS( Map.empty )
  } yield ProofCollection( m.toList.map( _.swap ).toMap )
}