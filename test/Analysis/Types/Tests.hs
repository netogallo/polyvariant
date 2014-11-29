module Analysis.Types.Tests(
  effRedUnionEq,
  effNormalizeEquivalent,
  annNormalizeEquivalent
  ) where

import qualified Analysis.Types.AnnotationTests as AT
import qualified Analysis.Types.EffectTests as ET

effRedUnionEq = ET.redUnionEq
effNormalizeEquivalent = ET.normalizeEquivalent
annNormalizeEquivalent = AT.normalizeEquivalent
