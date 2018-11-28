package gapt.formats.json

import cats.{ Eval, Later }
import gapt.proofs.DagProof
import io.circe.Decoder.Result
import io.circe._
import io.circe.KeyEncoder._
import cats.implicits._

import scala.collection.immutable.ListMap

/**
 * Wraps a map from proofs to integers. Each proof must be mapped to a
 * higher number than its subproofs.
 */
private[json] class ProofCollection[P <: DagProof[P]] private ( val proofMap: Map[P, Int] ) extends AnyVal

private[json] object ProofCollection {
  /**
   * Creates a [[ProofCollection]] from a proof by
   * enumerating all its subproofs in post order, disregarding duplicates.
   */
  private[json] def apply[P <: DagProof[P]]( p: P ): ProofCollection[P] = ProofCollection( p.dagLike.postOrder.zipWithIndex.toMap )

  /**
   * Creates a [[ProofCollection]] from a map. Each proof
   * must be mapped to a higher number than its subproofs.
   */
  private[json] def apply[P <: DagProof[P]]( m: Map[P, Int] ): ProofCollection[P] = {
    require( m.forall {
      case ( p, i ) =>
        p.immediateSubProofs.forall( q => m.contains( q ) && m( q ) < i )
    } )

    new ProofCollection( m )
  }
}

private[json] object ProofCollectionCodec {
  /**
   * Encodes a proof collection
   */
  private[json] def proofCollectionEncoder[P <: DagProof[P]](
    encodeProof: Encoder[P] => Encoder[P] ): Encoder[ProofCollection[P]] = { coll =>
    val numEncoder: Encoder[P] = p => Json.fromInt( coll.proofMap( p ) )
    val encodeProofWithName: Encoder[P] = p =>
      encodeProof( numEncoder )( p ).mapObject( ( "name", Json.fromString( s"${p.longName}" ) ) +: _ )

    Encoder.encodeMap[Int, P]( implicitly, encodeProofWithName )(
      ListMap( coll.proofMap.toVector.map( _.swap ).sortBy( _._1 ): _* ) )
  }

  /**
   * Decodes a proof collection.
   */
  private[json] def proofCollectionDecoder[P <: DagProof[P]](
    decodeProof: ( String, ACursor, Decoder[P] ) => Result[P] ): Decoder[ProofCollection[P]] = Decoder.decodeMap[Int, Json] emap { jsonMap =>
    lazy val proofMap: Map[Int, Eval[Result[P]]] = jsonMap map { case ( i, json ) => ( i, Later( json.as[P] ) ) }
    lazy val numDecoder: Decoder[P] = Decoder.decodeInt.emap { i =>
      proofMap.get( i ) match {
        case Some( e ) => e.value.leftMap( _.message )
        case None      => Left( s"Proof $i not found" )
      }
    }

    implicit lazy val proofDecoder: Decoder[P] = c => {
      val d = c.downField( "name" )
      d.as[String].flatMap { name =>
        val e = d.delete
        decodeProof( name, e, numDecoder )
      }
    }

    val forced: List[( Result[P], Int )] = proofMap.toList.map {
      case ( i, e ) => ( e.value, i )
    }

    val resultList: Result[List[( P, Int )]] = forced.traverse[Result, ( P, Int )] {
      case ( Left( f ), i )  => Left( f )
      case ( Right( p ), i ) => Right( ( p, i ) )
    }

    resultList.leftMap( _.message ).map( l => ProofCollection( l.toMap ) )
  }
}