module GhcPlugins.Util (coreTransformerPlugin) where

import GhcPlugins

coreTransformerPlugin :: String -> PluginPass -> Plugin
coreTransformerPlugin name pass =
  defaultPlugin{ installCoreToDos = \_ todos ->
                   (CoreDoPluginPass name pass : todos) <$ reinitializeGlobals }
