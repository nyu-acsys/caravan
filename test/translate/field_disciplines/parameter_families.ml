module type Field = sig
  type 'a t = { mutable value : 'a [@caravan.frozen] }
end

module type View = sig
  include Field
end

module First : View = struct
  type 'a t = { mutable value : 'a }
end

module Second : View = struct
  type 'a t = { mutable value : 'a }
end

module Use (X : View) = struct
  let id (value : int) = value
end

module Left = Use (First)
module Alias = First
module Same = Use (Alias)
module Right = Use (Second)

module Forward (X : View) = struct
  module Inner = Use (X)

  let id (value : int) = Inner.id value
end

module Forwarded = Forward (First)

module Both (X : View) (Y : View) = struct
  module Inner = Use (Y)

  let id (value : int) = Inner.id value
end

module Distinct = Both (First) (Second)
