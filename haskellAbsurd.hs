data False
type Not a = a -> False

data Liar = Liar (Not Liar)


honest :: Not Liar
honest l@(Liar p) = p l

absurd :: False
absurd = honest $ Liar honest
