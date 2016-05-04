module FStar.String
  open System

  let make n c = new String(c, n)
  let strcat x y = x ^ y
  let split seps (s:String) = s.Split(seps)
  let compare (x:String) (y:String) = String.Compare(x, y)
  let concat sep (s:String list) = String.Join(sep, s)
  let length (s:String) = s.Length
  let sub (s:String) i j = s.Substring(i, j - i)
  let get (s:String) i = s.[i]
  let collect = Core.String.collect
  let lowercase (s:String) = s.ToLower()
  let substring (s:String) i len = s.Substring(i, len)
