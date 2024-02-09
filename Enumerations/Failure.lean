universe u v

class Failure (F : Type u → Type v) where
  failure {α : Type u}: F α

instance (F : Type u → Type v) [Alternative F] : Failure F where
  failure := failure
