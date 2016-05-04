module FStar_Char 
  open System

  let lowercase = Char.ToLower
  let uppercase = Char.ToUpper
  let int_of_char (x:char) = Convert.ToInt32 x
  let char_of_int (x:int) = Convert.ToChar x
