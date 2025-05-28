Definition SHVZK_real p :
  game (Transcript p) :=
  [module no_locs ;
    #def #[ TRANSCRIPT ] ('(h, w, e) : 'input p) : ('transcript p) {
      #assert p.(R) h w ;;
      '(a, s) ← p.(commit) h w ;;
      z ← p.(response) h w a s e ;;
      @ret (chTranscript p) (h, a, e, z)
    }
  ].