module Plugin.DumpModules (plugin) where

import GhcPlugins
import GhcPlugins.Util
import PrintModGuts

plugin :: Plugin
plugin = coreTransformerPlugin "Dump Modules" $ \guts -> do
    putMsg $ text "=========== Dump Modules Start ==========="
    printModGuts fullInfo guts
    putMsg $ text "=========== Dump Modules Stop ============"
    pure guts
