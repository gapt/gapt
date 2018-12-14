package gapt.examples

object sqrtAutomaticExtractedWithoutShapeless extends Script {
  def s( x: Int ) = x + 1

  def mul( x: Int )( y: Int ) = x * y

  def leq( x: Int )( y: Int ) = x <= y

  def pow2( x: Int ) = x * x

  def pi2[A, B]( p: ( A, B ) ) = p._2

  sealed trait Sum[A, B]

  final case class Inr[A, B]( v: B ) extends Sum[A, B]

  def matchSum[A, B, C]( p1: Sum[A, B] )( p2: A => C )( p3: B => C ) = {
    p1 match {
      case Inl( a ) => p2( a )
      case Inr( b ) => p3( b )
    }
  }

  def eq[X]( x: X )( y: X ) = x == y

  def lt( x: Int )( y: Int ) = x < y

  final case class Inl[A, B]( v: A ) extends Sum[A, B]

  def natRec[A]( p1: A )( p2: ( Int => A => A ) )( p3: Int ): A = {
    if ( p3 == 0 ) {
      p1
    } else {
      p2( p3 - 1 )( natRec( p1 )( p2 )( p3 - 1 ) )
    }
  }

  case class Exn[A]( v: A, id: Option[Int] ) extends Exception

  def exception[A]( v: A )( id: Option[Int] = None ) = new Exn( v, id )

  def pi1[A, B]( p: ( A, B ) ) = p._1

  def pair[A, B]( p0: A )( p1: B ): Tuple2[A, B] = ( p0, p1 )

  def efq[B]( p: Throwable ): B = throw p

  val prog = ( {
    vLambda_66: ( Int => Unit ) =>
      ( {
        vLambda_65: ( Int => Unit ) =>
          ( {
            vLambda_56: ( Int => ( Int => ( Unit => Sum[Unit, Unit] ) ) ) =>
              ( {
                vLambda_50: ( Int => Unit ) =>
                  ( {
                    vLambda_61: ( Int => ( Int => ( Int => ( Tuple2[Unit, Unit] => Unit ) ) ) ) =>
                      ( {
                        vLambda_49: ( Int => Unit ) =>
                          ( {
                            vLambda_54: ( Int => ( Int => Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] ) ) =>
                              ( {
                                v_2: Int =>
                                  ( {
                                    vLambda_1: Unit =>
                                      ( {
                                        vLambda_3: Unit =>
                                          ( {
                                            vLambda_64: ( Int => Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] ) =>
                                              ( {
                                                vLambda_63: Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] =>
                                                  ( {
                                                    vLambda_2: Unit =>
                                                      ( {
                                                        vLambda_5: ( Sum[Unit, Unit] => Unit ) =>
                                                          ( {
                                                            vLambda_62: ( Unit => Sum[Unit, Unit] ) =>
                                                              ( {
                                                                vLambda_0: ( Int => Tuple2[Int, Tuple2[Unit, Unit]] ) =>
                                                                  ( {
                                                                    vLambda: Tuple2[Int, Tuple2[Unit, Unit]] => vLambda
                                                                  } )( vLambda_0( v_2 ) )
                                                              } )( ( {
                                                                n: Int =>
                                                                  natRec[Tuple2[Int, Tuple2[Unit, Unit]]]( pair[Int, Tuple2[Unit, Unit]]( 0 )( pair[Unit, Unit]( () )( ( {
                                                                    vLambda_4: Unit => ()
                                                                  } )( vLambda_5( Inl[Unit, Unit]( () ) ) ) ) ) )( ( {
                                                                    v_0: Int =>
                                                                      ( {
                                                                        vLambda_6: Tuple2[Int, Tuple2[Unit, Unit]] =>
                                                                          ( {
                                                                            vLambda_58: ( Int => ( Int => ( Tuple2[Unit, Unit] => Unit ) ) ) =>
                                                                              ( {
                                                                                vLambda_60: ( Int => ( Int => ( Tuple2[Unit, Unit] => Unit ) ) ) =>
                                                                                  ( {
                                                                                    vLambda_59: ( Int => ( Tuple2[Unit, Unit] => Unit ) ) =>
                                                                                      ( {
                                                                                        vLambda_32: ( Tuple2[Unit, Unit] => Unit ) =>
                                                                                          ( {
                                                                                            vLambda_57: ( Int => ( Tuple2[Unit, Unit] => Unit ) ) =>
                                                                                              ( {
                                                                                                vLambda_16: ( Tuple2[Unit, Unit] => Unit ) =>
                                                                                                  ( {
                                                                                                    vLambda_55: ( Int => ( Unit => Sum[Unit, Unit] ) ) =>
                                                                                                      ( {
                                                                                                        vLambda_21: ( Unit => Sum[Unit, Unit] ) =>
                                                                                                          ( {
                                                                                                            vLambda_51: ( Int => Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] ) =>
                                                                                                              ( {
                                                                                                                vLambda_52: ( Int => Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] ) =>
                                                                                                                  ( {
                                                                                                                    vLambda_53: ( Int => Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] ) =>
                                                                                                                      ( {
                                                                                                                        vLambda_47: Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] =>
                                                                                                                          ( {
                                                                                                                            vLambda_45: Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] =>
                                                                                                                              ( {
                                                                                                                                vLambda_43: Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] =>
                                                                                                                                  ( {
                                                                                                                                    vLambda_41: Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] =>
                                                                                                                                      ( {
                                                                                                                                        vLambda_19: Unit =>
                                                                                                                                          ( {
                                                                                                                                            vLambda_18: Unit =>
                                                                                                                                              ( {
                                                                                                                                                vLambda_29: Unit =>
                                                                                                                                                  try {
                                                                                                                                                    ( {
                                                                                                                                                      vLambda_9: ( Tuple2[Int, Tuple2[Unit, Unit]] => Exception ) =>
                                                                                                                                                        pair[Int, Tuple2[Unit, Unit]]( pi1[Int, Tuple2[Unit, Unit]]( vLambda_6 ) )(
                                                                                                                                                          try {
                                                                                                                                                            ( {
                                                                                                                                                              vLambda_11: ( Tuple2[Unit, Unit] => Exception ) =>
                                                                                                                                                                efq[Tuple2[Unit, Unit]]( vLambda_9( pair[Int, Tuple2[Unit, Unit]]( s( pi1[Int, Tuple2[Unit, Unit]]( vLambda_6 ) ) )( ( {
                                                                                                                                                                  vLambda_35: Unit =>
                                                                                                                                                                    ( {
                                                                                                                                                                      vLambda_22: Unit =>
                                                                                                                                                                        ( {
                                                                                                                                                                          vLambda_28: ( Sum[Unit, Unit] => Unit ) =>
                                                                                                                                                                            ( {
                                                                                                                                                                              vLambda_46: ( Unit => Sum[Unit, Unit] ) =>
                                                                                                                                                                                ( {
                                                                                                                                                                                  vLambda_30: ( Sum[Unit, Unit] => Unit ) =>
                                                                                                                                                                                    ( {
                                                                                                                                                                                      vLambda_44: ( Unit => Sum[Unit, Unit] ) =>
                                                                                                                                                                                        ( {
                                                                                                                                                                                          vLambda_42: ( Sum[Unit, Unit] => Unit ) =>
                                                                                                                                                                                            ( {
                                                                                                                                                                                              vLambda_34: ( Unit => Sum[Unit, Unit] ) =>
                                                                                                                                                                                                ( {
                                                                                                                                                                                                  vLambda_39: ( Sum[Unit, Unit] => Unit ) =>
                                                                                                                                                                                                    ( {
                                                                                                                                                                                                      vLambda_40: ( Unit => Sum[Unit, Unit] ) =>
                                                                                                                                                                                                        try {
                                                                                                                                                                                                          ( {
                                                                                                                                                                                                            vLambda_12: ( Tuple2[Unit, Unit] => Exception ) =>
                                                                                                                                                                                                              efq[Tuple2[Unit, Unit]]( vLambda_11(
                                                                                                                                                                                                                try {
                                                                                                                                                                                                                  ( {
                                                                                                                                                                                                                    vLambda_11: ( Tuple2[Unit, Unit] => Exception ) =>
                                                                                                                                                                                                                      try {
                                                                                                                                                                                                                        ( {
                                                                                                                                                                                                                          vLambda_11: ( Tuple2[Unit, Unit] => Exception ) =>
                                                                                                                                                                                                                            efq[Tuple2[Unit, Unit]]( vLambda_12( pair[Unit, Unit](
                                                                                                                                                                                                                              try {
                                                                                                                                                                                                                                ( {
                                                                                                                                                                                                                                  vLambda_15: ( Unit => Exception ) =>
                                                                                                                                                                                                                                    efq[Unit]( vLambda_11( pair[Unit, Unit]( ( {
                                                                                                                                                                                                                                      vLambda_14: Sum[Unit, Unit] =>
                                                                                                                                                                                                                                        matchSum( vLambda_14 )( ( {
                                                                                                                                                                                                                                          vLambda_17: Unit =>
                                                                                                                                                                                                                                            efq[Unit]( vLambda_15( ( {
                                                                                                                                                                                                                                              vLambda_13: Unit => vLambda_13
                                                                                                                                                                                                                                            } )( vLambda_16( pair[Unit, Unit]( () )( vLambda_19 ) ) ) ) )
                                                                                                                                                                                                                                        } ) )( ( {
                                                                                                                                                                                                                                          vLambda_20: Unit => vLambda_20
                                                                                                                                                                                                                                        } ) )
                                                                                                                                                                                                                                    } )( vLambda_21( vLambda_22 ) ) )( ( {
                                                                                                                                                                                                                                      vLambda_24: Sum[Unit, Unit] =>
                                                                                                                                                                                                                                        try {
                                                                                                                                                                                                                                          ( {
                                                                                                                                                                                                                                            vLambda_25: ( Unit => Exception ) =>
                                                                                                                                                                                                                                              matchSum( vLambda_24 )( ( {
                                                                                                                                                                                                                                                vLambda_26: Unit =>
                                                                                                                                                                                                                                                  efq[Unit]( vLambda_25( ( {
                                                                                                                                                                                                                                                    vLambda_27: Unit => ()
                                                                                                                                                                                                                                                  } )( vLambda_28( Inr[Unit, Unit]( vLambda_29 ) ) ) ) )
                                                                                                                                                                                                                                              } ) )( ( {
                                                                                                                                                                                                                                                vLambda_33: Unit =>
                                                                                                                                                                                                                                                  ( {
                                                                                                                                                                                                                                                    vLambda_23: Unit => vLambda_23
                                                                                                                                                                                                                                                  } )( vLambda_30( Inr[Unit, Unit]( ( {
                                                                                                                                                                                                                                                    vLambda_31: Unit => vLambda_31
                                                                                                                                                                                                                                                  } )( vLambda_32( pair[Unit, Unit]( vLambda_33 )( vLambda_29 ) ) ) ) ) )
                                                                                                                                                                                                                                              } ) )
                                                                                                                                                                                                                                          } )( exception[Unit]( _ )( Some( 6 ) ) )
                                                                                                                                                                                                                                        } catch {
                                                                                                                                                                                                                                          case Exn( v: Unit, Some( id ) ) if id == 6 => {
                                                                                                                                                                                                                                            //println( "thrown at " + e.id + " caught at 6" )
                                                                                                                                                                                                                                            ( {
                                                                                                                                                                                                                                              vLambda_23: Unit => vLambda_23
                                                                                                                                                                                                                                            } )( v )
                                                                                                                                                                                                                                          }
                                                                                                                                                                                                                                          case e => {
                                                                                                                                                                                                                                            //println("throwing further at 6")
                                                                                                                                                                                                                                            throw e
                                                                                                                                                                                                                                          }
                                                                                                                                                                                                                                        }
                                                                                                                                                                                                                                    } )( vLambda_34( vLambda_35 ) ) ) ) )
                                                                                                                                                                                                                                } )( exception[Unit]( _ )( Some( 5 ) ) )
                                                                                                                                                                                                                              } catch {
                                                                                                                                                                                                                                case Exn( v: Unit, Some( id ) ) if id == 5 => {
                                                                                                                                                                                                                                  //println( "thrown at " + e.id + " caught at 5" )
                                                                                                                                                                                                                                  ( {
                                                                                                                                                                                                                                    vLambda_13: Unit => vLambda_13
                                                                                                                                                                                                                                  } )( v )
                                                                                                                                                                                                                                }
                                                                                                                                                                                                                                case e => {
                                                                                                                                                                                                                                  //println("throwing further at 5")
                                                                                                                                                                                                                                  throw e
                                                                                                                                                                                                                                }
                                                                                                                                                                                                                              } )(
                                                                                                                                                                                                                                try {
                                                                                                                                                                                                                                  ( {
                                                                                                                                                                                                                                    vLambda_37: ( Unit => Exception ) =>
                                                                                                                                                                                                                                      efq[Unit]( vLambda_11( pair[Unit, Unit]( ( {
                                                                                                                                                                                                                                        vLambda_38: Unit =>
                                                                                                                                                                                                                                          ( {
                                                                                                                                                                                                                                            vLambda_14: Sum[Unit, Unit] =>
                                                                                                                                                                                                                                              matchSum( vLambda_14 )( ( {
                                                                                                                                                                                                                                                vLambda_17: Unit => efq[Unit]( vLambda_37( () ) )
                                                                                                                                                                                                                                              } ) )( ( {
                                                                                                                                                                                                                                                vLambda_20: Unit => vLambda_20
                                                                                                                                                                                                                                              } ) )
                                                                                                                                                                                                                                          } )( vLambda_21( vLambda_22 ) )
                                                                                                                                                                                                                                      } )( vLambda_39( Inl[Unit, Unit]( () ) ) ) )( ( {
                                                                                                                                                                                                                                        vLambda_24: Sum[Unit, Unit] =>
                                                                                                                                                                                                                                          try {
                                                                                                                                                                                                                                            ( {
                                                                                                                                                                                                                                              vLambda_25: ( Unit => Exception ) =>
                                                                                                                                                                                                                                                matchSum( vLambda_24 )( ( {
                                                                                                                                                                                                                                                  vLambda_26: Unit =>
                                                                                                                                                                                                                                                    efq[Unit]( vLambda_25( ( {
                                                                                                                                                                                                                                                      vLambda_27: Unit => ()
                                                                                                                                                                                                                                                    } )( vLambda_28( Inr[Unit, Unit]( vLambda_29 ) ) ) ) )
                                                                                                                                                                                                                                                } ) )( ( {
                                                                                                                                                                                                                                                  vLambda_33: Unit =>
                                                                                                                                                                                                                                                    ( {
                                                                                                                                                                                                                                                      vLambda_23: Unit => vLambda_23
                                                                                                                                                                                                                                                    } )( vLambda_30( Inr[Unit, Unit]( ( {
                                                                                                                                                                                                                                                      vLambda_31: Unit => vLambda_31
                                                                                                                                                                                                                                                    } )( vLambda_32( pair[Unit, Unit]( vLambda_33 )( vLambda_29 ) ) ) ) ) )
                                                                                                                                                                                                                                                } ) )
                                                                                                                                                                                                                                            } )( exception[Unit]( _ )( Some( 8 ) ) )
                                                                                                                                                                                                                                          } catch {
                                                                                                                                                                                                                                            case Exn( v: Unit, Some( id ) ) if id == 8 => {
                                                                                                                                                                                                                                              //println( "thrown at " + e.id + " caught at 8" )
                                                                                                                                                                                                                                              ( {
                                                                                                                                                                                                                                                vLambda_23: Unit => vLambda_23
                                                                                                                                                                                                                                              } )( v )
                                                                                                                                                                                                                                            }
                                                                                                                                                                                                                                            case e => {
                                                                                                                                                                                                                                              //println("throwing further at 8")
                                                                                                                                                                                                                                              throw e
                                                                                                                                                                                                                                            }
                                                                                                                                                                                                                                          }
                                                                                                                                                                                                                                      } )( vLambda_34( vLambda_35 ) ) ) ) )
                                                                                                                                                                                                                                  } )( exception[Unit]( _ )( Some( 7 ) ) )
                                                                                                                                                                                                                                } catch {
                                                                                                                                                                                                                                  case Exn( v: Unit, Some( id ) ) if id == 7 => {
                                                                                                                                                                                                                                    //println( "thrown at " + e.id + " caught at 7" )
                                                                                                                                                                                                                                    ( {
                                                                                                                                                                                                                                      vLambda_36: Unit => vLambda_36
                                                                                                                                                                                                                                    } )( v )
                                                                                                                                                                                                                                  }
                                                                                                                                                                                                                                  case e => {
                                                                                                                                                                                                                                    //println("throwing further at 7")
                                                                                                                                                                                                                                    throw e
                                                                                                                                                                                                                                  }
                                                                                                                                                                                                                                } ) ) )
                                                                                                                                                                                                                        } )( exception[Tuple2[Unit, Unit]]( _ )( Some( 4 ) ) )
                                                                                                                                                                                                                      } catch {
                                                                                                                                                                                                                        case Exn( v: Tuple2[Unit, Unit], Some( id ) ) if id == 4 => {
                                                                                                                                                                                                                          //println( "thrown at " + e.id + " caught at 4" )
                                                                                                                                                                                                                          ( {
                                                                                                                                                                                                                            vLambda_8: Tuple2[Unit, Unit] => vLambda_8
                                                                                                                                                                                                                          } )( v )
                                                                                                                                                                                                                        }
                                                                                                                                                                                                                        case e => {
                                                                                                                                                                                                                          //println("throwing further at 4")
                                                                                                                                                                                                                          throw e
                                                                                                                                                                                                                        }
                                                                                                                                                                                                                      }
                                                                                                                                                                                                                  } )( exception[Tuple2[Unit, Unit]]( _ )( Some( 3 ) ) )
                                                                                                                                                                                                                } catch {
                                                                                                                                                                                                                  case Exn( v: Tuple2[Unit, Unit], Some( id ) ) if id == 3 => {
                                                                                                                                                                                                                    //println( "thrown at " + e.id + " caught at 3" )
                                                                                                                                                                                                                    ( {
                                                                                                                                                                                                                      vLambda_8: Tuple2[Unit, Unit] => vLambda_8
                                                                                                                                                                                                                    } )( v )
                                                                                                                                                                                                                  }
                                                                                                                                                                                                                  case e => {
                                                                                                                                                                                                                    //println("throwing further at 3")
                                                                                                                                                                                                                    throw e
                                                                                                                                                                                                                  }
                                                                                                                                                                                                                } ) )
                                                                                                                                                                                                          } )( exception[Tuple2[Unit, Unit]]( _ )( Some( 2 ) ) )
                                                                                                                                                                                                        } catch {
                                                                                                                                                                                                          case Exn( v: Tuple2[Unit, Unit], Some( id ) ) if id == 2 => {
                                                                                                                                                                                                            //println( "thrown at " + e.id + " caught at 2" )
                                                                                                                                                                                                            ( {
                                                                                                                                                                                                              vLambda_10: Tuple2[Unit, Unit] => vLambda_10
                                                                                                                                                                                                            } )( v )
                                                                                                                                                                                                          }
                                                                                                                                                                                                          case e => {
                                                                                                                                                                                                            //println("throwing further at 2")
                                                                                                                                                                                                            throw e
                                                                                                                                                                                                          }
                                                                                                                                                                                                        }
                                                                                                                                                                                                    } )( pi1[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( vLambda_41 ) )
                                                                                                                                                                                                } )( pi2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( vLambda_41 ) )
                                                                                                                                                                                            } )( pi1[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( vLambda_43 ) )
                                                                                                                                                                                        } )( pi2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( vLambda_43 ) )
                                                                                                                                                                                    } )( pi1[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( vLambda_45 ) )
                                                                                                                                                                                } )( pi2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( vLambda_45 ) )
                                                                                                                                                                            } )( pi1[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( vLambda_47 ) )
                                                                                                                                                                        } )( pi2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( vLambda_47 ) )
                                                                                                                                                                    } )( pi1[Unit, Unit]( pi2[Int, Tuple2[Unit, Unit]]( vLambda_6 ) ) )
                                                                                                                                                                } )( pi2[Unit, Unit]( pi2[Int, Tuple2[Unit, Unit]]( vLambda_6 ) ) ) ) ) )
                                                                                                                                                            } )( exception[Tuple2[Unit, Unit]]( _ )( Some( 1 ) ) )
                                                                                                                                                          } catch {
                                                                                                                                                            case Exn( v: Tuple2[Unit, Unit], Some( id ) ) if id == 1 => {
                                                                                                                                                              //println( "thrown at " + e.id + " caught at 1" )
                                                                                                                                                              ( {
                                                                                                                                                                vLambda_8: Tuple2[Unit, Unit] => vLambda_8
                                                                                                                                                              } )( v )
                                                                                                                                                            }
                                                                                                                                                            case e => {
                                                                                                                                                              //println("throwing further at 1")
                                                                                                                                                              throw e
                                                                                                                                                            }
                                                                                                                                                          } )
                                                                                                                                                    } )( exception[Tuple2[Int, Tuple2[Unit, Unit]]]( _ )( Some( 0 ) ) )
                                                                                                                                                  } catch {
                                                                                                                                                    case Exn( v: Tuple2[Int, Tuple2[Unit, Unit]], Some( id ) ) if id == 0 => {
                                                                                                                                                      //println( "thrown at " + e.id + " caught at 0" )
                                                                                                                                                      ( {
                                                                                                                                                        vLambda_7: Tuple2[Int, Tuple2[Unit, Unit]] => vLambda_7
                                                                                                                                                      } )( v )
                                                                                                                                                    }
                                                                                                                                                    case e => {
                                                                                                                                                      //println("throwing further at 0")
                                                                                                                                                      throw e
                                                                                                                                                    }
                                                                                                                                                  }
                                                                                                                                              } )( vLambda_49( v_0 ) )
                                                                                                                                          } )( vLambda_49( s( v_0 ) ) )
                                                                                                                                      } )( vLambda_50( pi1[Int, Tuple2[Unit, Unit]]( vLambda_6 ) ) )
                                                                                                                                  } )( vLambda_51( s( v_0 ) ) )
                                                                                                                              } )( vLambda_52( v_0 ) )
                                                                                                                          } )( vLambda_52( s( v_0 ) ) )
                                                                                                                      } )( vLambda_53( s( v_0 ) ) )
                                                                                                                  } )( vLambda_54( v_0 ) )
                                                                                                              } )( vLambda_54( mul( pi1[Int, Tuple2[Unit, Unit]]( vLambda_6 ) )( pi1[Int, Tuple2[Unit, Unit]]( vLambda_6 ) ) ) )
                                                                                                          } )( vLambda_54( s( v_0 ) ) )
                                                                                                      } )( vLambda_55( mul( s( pi1[Int, Tuple2[Unit, Unit]]( vLambda_6 ) ) )( s( pi1[Int, Tuple2[Unit, Unit]]( vLambda_6 ) ) ) ) )
                                                                                                  } )( vLambda_56( v_0 ) )
                                                                                              } )( vLambda_57( mul( s( s( pi1[Int, Tuple2[Unit, Unit]]( vLambda_6 ) ) ) )( s( s( pi1[Int, Tuple2[Unit, Unit]]( vLambda_6 ) ) ) ) ) )
                                                                                          } )( vLambda_58( s( mul( s( pi1[Int, Tuple2[Unit, Unit]]( vLambda_6 ) ) )( s( pi1[Int, Tuple2[Unit, Unit]]( vLambda_6 ) ) ) ) ) )
                                                                                      } )( vLambda_59( s( v_0 ) ) )
                                                                                  } )( vLambda_60( v_0 ) )
                                                                              } )( vLambda_61( mul( pi1[Int, Tuple2[Unit, Unit]]( vLambda_6 ) )( pi1[Int, Tuple2[Unit, Unit]]( vLambda_6 ) ) ) )
                                                                          } )( vLambda_61( s( v_0 ) ) )
                                                                      } )
                                                                  } ) )( n )
                                                              } ) )
                                                          } )( pi1[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( vLambda_63 ) )
                                                      } )( pi2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( vLambda_63 ) )
                                                  } )( vLambda_49( 0 ) )
                                              } )( vLambda_64( 0 ) )
                                          } )( vLambda_54( 0 ) )
                                      } )( vLambda_65( 0 ) )
                                  } )( vLambda_66( s( 0 ) ) )
                              } )
                          } )
                      } )
                  } )
              } )
          } )
      } )
  } )

  val arg1 = { _: Int => () }
  val arg3 = { _: Int => { _: Int => { _: Int => { _: Tuple2[Unit, Unit] => () } } } }
  val arg4 = { x: Int =>
    { y: Int =>
      { _: Unit =>
        //println( s"v_59: x=$x, y=$y" )
        if ( s( x ) == y ) {
          Inl[Unit, Unit]( () )
        } else if ( s( x ) < y ) {
          Inr[Unit, Unit]( () )
        } else {
          // Don't care
          Inr[Unit, Unit]( () )
        }
      }
    }
  }
  val arg10 = { x: Int =>
    { ( y: Int ) =>
      ( { _: Unit =>
        //println( s"v: x=$x, y=$y" )
        if ( x == y ) {
          Inl[Unit, Unit]( () )
        } else if ( x < y ) {
          Inr[Unit, Unit]( () )
        } else {
          // Don't care
          Inr[Unit, Unit]( () )
        }
      }, { _: Sum[Unit, Unit] => () } )
    }
  }

  val realProg = prog( arg1 )( arg1 )( arg4 )( arg1 )( arg3 )( arg1 )( arg10 )

  0 to 4 foreach ( i => println( s"floor(sqrt($i)) = ${realProg( i )._1}\n" ) )
  println( "Testing 1000 inputs" )
  0 to 1000 foreach ( i => {
    if ( Math.floor( Math.sqrt( i ) ).toInt != realProg( i )._1 ) {
      throw new Exception( s"realProg failed at input $i." )
    }
  } )
}