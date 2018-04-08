$(OUT)/Data/OldList.v: $(OUT)/GHC/Num.h2ci
$(OUT)/Data/Proxy.v: $(OUT)/GHC/Enum.h2ci
$(OUT)/Data/Traversable.v: $(OUT)/Data/Foldable.h2ci
$(OUT)/Data/Traversable.v: $(OUT)/Data/Functor/Identity.h2ci
$(OUT)/Data/Traversable.v: $(OUT)/Data/Functor/Const.h2ci
$(OUT)/Data/Foldable.v: $(OUT)/Data/SemigroupInternal.h2ci
$(OUT)/Data/Functor/Const.v: $(OUT)/Data/Foldable.h2ci
$(OUT)/Data/Functor/Identity.v: $(OUT)/Data/Foldable.h2ci
