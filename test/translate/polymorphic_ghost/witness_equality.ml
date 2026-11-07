type _ witness = Ref : int ref witness | Number : int witness

let choose : type r. int ref -> r witness -> r =
 fun cell witness -> match witness with Ref -> cell | Number -> 0
