"""Small AlphaZero-style policy+value network, sized for training on a
laptop GPU via MLX.

Architecture: a convolutional "trunk" (stem conv + a stack of residual
blocks) shared by two output heads, a policy head and a value head. This is
the same shape as AlphaZero/Leela Zero, minus their scale:

  input (8, 8, 17)
        |
   stem conv+BN+ReLU
        |
   [ResBlock] x num_blocks   <- shared trunk
       /            \
 policy head     value head
  (4096 logits)   (scalar, tanh)

Why this shape, not something simpler (e.g. an MLP on a flattened board) or
fancier (e.g. a transformer over squares):

- **Convolutions fit chess geometrically.** Piece values and tactics (forks,
  pins, mobility) are local, translation-ish patterns on an 8x8 grid — "a
  knight attacks these relative squares" holds regardless of where the
  knight is. A CNN's weight sharing exploits exactly that, the way it does
  for images. An MLP would have to relearn every pattern per square; a
  transformer's global attention is more than this board needs and costs
  far more compute per parameter, which matters when the target is fast
  laptop-GPU training via MLX rather than a data-center run.
- **Residual blocks, not a plain deep stack.** They're what made AlphaZero's
  depth trainable at all — the skip connection lets gradients pass straight
  through, which stabilizes training so we can add depth (`num_blocks`) to
  trade capacity for compute without it degrading.
- **Two heads on one trunk, not two separate networks.** Board understanding
  (piece safety, king exposure, space) is the same feature set a good move
  and a good evaluation both depend on, so sharing the trunk gets the value
  head's training signal to double as regularization for the policy head
  (and vice versa) — normal practice for AlphaZero-style nets, and it halves
  the conv compute versus two independent networks.
- **Policy head outputs a flat 4096-way distribution** (`from_square * 64 +
  to_square`, see `encoding.py`) rather than AlphaZero's full 73-plane move
  encoding. That richer encoding exists to disambiguate underpromotions and
  knight-move-shaped queen moves from a *per-square* policy map; since we
  instead flatten straight to a single from/to logit vector, that
  disambiguation isn't needed — collapsing underpromotions to "queen" (see
  `encoding.py`) is the only thing given up, and it's a rare-enough case to
  trade away for a much simpler head.
- **Value head is a narrower bottleneck** (fewer conv channels, smaller FC)
  than the policy head, because a single scalar needs far less capacity to
  predict than a 4096-way distribution — sizing it down keeps params
  concentrated where they help most.
- **`channels`/`num_blocks` are the knobs to scale by**, wired straight
  through from `train.py`'s CLI flags: widen/deepen if the student
  plateaus below the teacher's ability and the Mac (or a Colab GPU, per the
  README) can afford it; shrink if training is too slow for iteration.
"""

import mlx.core as mx
import mlx.nn as nn

from encoding import NUM_PLANES, POLICY_SIZE


class ResBlock(nn.Module):
    """Two 3x3 convs with a skip connection (AlphaZero-style trunk block).

    The skip connection is what makes stacking many of these trainable:
    each block only has to learn a residual correction to its input rather
    than reconstruct the full signal, so gradients keep flowing to early
    blocks even as `num_blocks` grows.
    """

    def __init__(self, channels: int):
        super().__init__()
        self.conv1 = nn.Conv2d(channels, channels, kernel_size=3, padding=1)
        self.bn1 = nn.BatchNorm(channels)
        self.conv2 = nn.Conv2d(channels, channels, kernel_size=3, padding=1)
        self.bn2 = nn.BatchNorm(channels)

    def __call__(self, x: mx.array) -> mx.array:
        y = nn.relu(self.bn1(self.conv1(x)))
        y = self.bn2(self.conv2(y))
        return nn.relu(x + y)


class ChessNet(nn.Module):
    """Shared conv trunk with a policy head and a value head on top.

    `channels`/`num_blocks` control the trunk's width/depth and are the main
    capacity vs. training-speed knob (see module docstring).
    """

    def __init__(self, channels: int = 64, num_blocks: int = 4):
        super().__init__()
        self.stem_conv = nn.Conv2d(NUM_PLANES, channels, kernel_size=3, padding=1)
        self.stem_bn = nn.BatchNorm(channels)
        self.blocks = [ResBlock(channels) for _ in range(num_blocks)]

        # Policy head: 1x1 conv to mix channels down, then a single FC layer
        # to the flat 4096-way (from_square, to_square) move space.
        self.policy_conv = nn.Conv2d(channels, 32, kernel_size=1)
        self.policy_bn = nn.BatchNorm(32)
        self.policy_fc = nn.Linear(32 * 8 * 8, POLICY_SIZE)

        # Value head: narrower than the policy head — predicting one scalar
        # needs less capacity than a 4096-way distribution.
        self.value_conv = nn.Conv2d(channels, 8, kernel_size=1)
        self.value_bn = nn.BatchNorm(8)
        self.value_fc1 = nn.Linear(8 * 8 * 8, 64)
        self.value_fc2 = nn.Linear(64, 1)

    def __call__(self, x: mx.array) -> tuple[mx.array, mx.array]:
        x = nn.relu(self.stem_bn(self.stem_conv(x)))
        for block in self.blocks:
            x = block(x)

        p = nn.relu(self.policy_bn(self.policy_conv(x)))
        p = p.reshape(p.shape[0], -1)
        policy_logits = self.policy_fc(p)

        v = nn.relu(self.value_bn(self.value_conv(x)))
        v = v.reshape(v.shape[0], -1)
        v = nn.relu(self.value_fc1(v))
        value = mx.tanh(self.value_fc2(v)).reshape(-1)

        return policy_logits, value
