universe u v w

structure Data (Class : Type u → Type v → Type w) (α : Type u) : Type (max (v + 1) w) where
  imp : Type v
  [inst : Class α imp]
  value : imp
