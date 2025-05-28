Definition SHVZK_ideal p :
  game (Transcript p) :=
  [module no_locs ;
    #def #[ TRANSCRIPT ] ('(h, w, e) : 'input p) : ('transcript p) {
      #assert p.(R) h w ;;
      '(a, z) ← p.(simulate) h e ;;
      @ret (chTranscript p) (h, a, e, z)
    }
  ].