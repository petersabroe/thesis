Definition Call_Soundness (p: raw_sigExt) :
  module (Soundness p) (IBinding (sig_to_com p)) := 
  [module fset [:: key_loc (sig_to_com p) ] ;
      #def #[ INIT ] (_ : 'unit) : ('unit) {
        'k ← (sig_to_com p).(setup) ;;
        #put key_loc (sig_to_com p) := Some k ;;
        ret tt
      } ;

      #def #[ GET ] (_ : 'unit) : ('key (sig_to_com p)) {
        k ← getSome key_loc (sig_to_com p) ;;
        ret k
      } ;

      #def #[ BINDING ] ('(c, v, o, v', o') : 'binding (sig_to_com p)) : 'bool
        {
          h ← getSome (key_loc (sig_to_com p));; 
          #import {sig #[ SOUNDNESS ] : ('soundness p) → 'bool} as SOUND ;;
          'b ← SOUND ((h, c), ((v, o), (v', o'))) ;;
          ret b
        }
  ].