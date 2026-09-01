import type { ReactNode } from 'react';
import { ActivityIndicator, Pressable, StyleSheet, Text, View, type StyleProp, type ViewStyle } from 'react-native';
import { SafeAreaView } from 'react-native-safe-area-context';
import { Ionicons } from '@expo/vector-icons';
import { useTheme, radius, spacing, typography, elevation } from '../theme/theme';

export function Screen({ children, style }: { children: ReactNode; style?: StyleProp<ViewStyle> }) {
  const { colors } = useTheme();
  return (
    <SafeAreaView style={[{ flex: 1, backgroundColor: colors.background }, style]} edges={['top', 'left', 'right']}>
      {children}
    </SafeAreaView>
  );
}

export function ScreenHeader({ title, subtitle }: { title: string; subtitle?: string }) {
  const { colors } = useTheme();
  return (
    <View style={{ paddingHorizontal: spacing.lg, paddingTop: spacing.md, paddingBottom: spacing.sm }}>
      <Text style={[typography.title, { color: colors.textPrimary }]}>{title}</Text>
      {subtitle ? <Text style={[typography.body, { color: colors.textSecondary, marginTop: 2 }]}>{subtitle}</Text> : null}
    </View>
  );
}

export function SectionLabel({ children }: { children: ReactNode }) {
  const { colors } = useTheme();
  return (
    <Text style={[typography.caption, { color: colors.textMuted, textTransform: 'uppercase', marginBottom: spacing.sm }]}>
      {children}
    </Text>
  );
}

export function Card({ children, style }: { children: ReactNode; style?: StyleProp<ViewStyle> }) {
  const { colors } = useTheme();
  return (
    <View
      style={[
        {
          backgroundColor: colors.surface,
          borderRadius: radius.lg,
          borderWidth: StyleSheet.hairlineWidth,
          borderColor: colors.border,
          padding: spacing.lg,
        },
        elevation.card,
        style,
      ]}
    >
      {children}
    </View>
  );
}

type ButtonVariant = 'primary' | 'outline' | 'ghost' | 'danger';

export function Button({
  label,
  onPress,
  variant = 'primary',
  disabled,
  loading,
  icon,
  style,
}: {
  label: string;
  onPress: () => void;
  variant?: ButtonVariant;
  disabled?: boolean;
  loading?: boolean;
  icon?: keyof typeof Ionicons.glyphMap;
  style?: StyleProp<ViewStyle>;
}) {
  const { colors } = useTheme();
  const isDisabled = disabled || loading;

  const palette: Record<ButtonVariant, { bg: string; fg: string; border?: string }> = {
    primary: { bg: colors.primary, fg: colors.onPrimary },
    danger: { bg: colors.danger, fg: colors.onPrimary },
    outline: { bg: 'transparent', fg: colors.primary, border: colors.primary },
    ghost: { bg: 'transparent', fg: colors.textSecondary },
  };
  const p = palette[variant];

  return (
    <Pressable
      onPress={onPress}
      disabled={isDisabled}
      hitSlop={6}
      style={({ pressed }) => [
        styles.button,
        {
          backgroundColor: p.bg,
          borderWidth: p.border ? 1.5 : 0,
          borderColor: p.border,
          opacity: isDisabled ? 0.5 : pressed ? 0.85 : 1,
        },
        style,
      ]}
    >
      {loading ? (
        <ActivityIndicator size="small" color={p.fg} />
      ) : (
        <>
          {icon ? <Ionicons name={icon} size={17} color={p.fg} style={{ marginRight: 8 }} /> : null}
          <Text style={[typography.subtitle, { color: p.fg }]}>{label}</Text>
        </>
      )}
    </Pressable>
  );
}

export function IconButton({
  name,
  onPress,
  color,
  background,
  size = 40,
  disabled,
}: {
  name: keyof typeof Ionicons.glyphMap;
  onPress: () => void;
  color?: string;
  background?: string;
  size?: number;
  disabled?: boolean;
}) {
  const { colors } = useTheme();
  return (
    <Pressable
      onPress={onPress}
      disabled={disabled}
      hitSlop={8}
      style={({ pressed }) => ({
        width: size,
        height: size,
        borderRadius: size / 2,
        alignItems: 'center',
        justifyContent: 'center',
        backgroundColor: background ?? colors.surfaceAlt,
        opacity: disabled ? 0.4 : pressed ? 0.7 : 1,
      })}
    >
      <Ionicons name={name} size={size * 0.5} color={color ?? colors.textPrimary} />
    </Pressable>
  );
}

export function ProgressBar({ progress, color, trackColor }: { progress: number; color?: string; trackColor?: string }) {
  const { colors } = useTheme();
  const pct = Math.max(0, Math.min(1, progress));
  return (
    <View style={{ height: 6, borderRadius: radius.full, backgroundColor: trackColor ?? colors.surfaceAlt, overflow: 'hidden' }}>
      <View style={{ width: `${pct * 100}%`, height: '100%', borderRadius: radius.full, backgroundColor: color ?? colors.primary }} />
    </View>
  );
}

export function Chip({ label, tone = 'neutral' }: { label: string; tone?: 'neutral' | 'primary' | 'vision' | 'accent' }) {
  const { colors } = useTheme();
  const tones = {
    neutral: { bg: colors.surfaceAlt, fg: colors.textSecondary },
    primary: { bg: colors.primarySoft, fg: colors.primary },
    vision: { bg: colors.visionSoft, fg: colors.vision },
    accent: { bg: colors.accentSoft, fg: colors.accent },
  };
  const t = tones[tone];
  return (
    <View style={{ backgroundColor: t.bg, borderRadius: radius.full, paddingHorizontal: spacing.sm, paddingVertical: 3, alignSelf: 'flex-start' }}>
      <Text style={[typography.micro, { color: t.fg, textTransform: 'uppercase' }]}>{label}</Text>
    </View>
  );
}

export function EmptyState({ icon, title, subtitle }: { icon: keyof typeof Ionicons.glyphMap; title: string; subtitle?: string }) {
  const { colors } = useTheme();
  return (
    <View style={{ alignItems: 'center', justifyContent: 'center', paddingVertical: spacing.xxxl, gap: spacing.sm }}>
      <View style={{ width: 56, height: 56, borderRadius: 28, backgroundColor: colors.surfaceAlt, alignItems: 'center', justifyContent: 'center' }}>
        <Ionicons name={icon} size={26} color={colors.textMuted} />
      </View>
      <Text style={[typography.subtitle, { color: colors.textPrimary }]}>{title}</Text>
      {subtitle ? <Text style={[typography.body, { color: colors.textSecondary, textAlign: 'center', maxWidth: 260 }]}>{subtitle}</Text> : null}
    </View>
  );
}

const styles = StyleSheet.create({
  button: {
    flexDirection: 'row',
    alignItems: 'center',
    justifyContent: 'center',
    paddingVertical: 13,
    paddingHorizontal: spacing.lg,
    borderRadius: radius.md,
    minHeight: 48,
  },
});
