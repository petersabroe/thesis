Definition Call_Hardness (p: raw_sigExt) :
   module (IHardness p) (IBinding (sig_to_com p)) :=
  [module no_locs ;
      #def #[ INIT ] (_ : 'unit) : ('unit) {
        call INIT 'unit ('unit) tt ;;
        ret tt
      } ;

      #def #[ GET ] (_ : 'unit) : ('key (sig_to_com p)) 
        {
          #import {sig #[ GET ] : 'unit → 'statement p} as GETH ;;
          h ← GETH Datatypes.tt ;;
          ret h
        } ;
      #def #[ BINDING ] ('(c, v, o, v', o') : 'binding (sig_to_com p)) : 'bool
          {
            #import {sig #[ QUERY ] : ('witness p) → 'bool} as QUE ;;
            #import {sig #[ GET ] : 'unit → 'statement p} as GETH ;;
            h ← GETH tt ;;
            #assert p.(Sigma.verify) h c v o ;;
            #assert p.(Sigma.verify) h c v' o' ;;
            #assert v != v' ;;
            let ow := p.(extractor) h c v v' o o' in
            if ow is Some w 
              then 'b ← QUE w ;; ret b 
              else ret false
          }
    ].