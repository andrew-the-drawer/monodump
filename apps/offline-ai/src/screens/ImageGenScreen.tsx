import { StyleSheet, Text, TextInput, View } from 'react-native';
import { Button, Card, EmptyState, Screen, ScreenHeader } from '../components/ui';
import { useTheme, radius, spacing, typography } from '../theme/theme';

/**
 * No on-device Stable Diffusion backend exists yet — QNN/MNN (Android) and
 * Core ML (iOS) each need a bespoke native pipeline that isn't wired up.
 * This screen stays visible so the tab structure matches the product, but
 * generation is disabled rather than silently pretending to work.
 */
export default function ImageGenScreen() {
  const { colors } = useTheme();

  return (
    <Screen>
      <ScreenHeader title="Image" subtitle="Generate images fully on-device" />
      <View style={{ paddingHorizontal: spacing.lg, gap: spacing.md, flex: 1 }}>
        <Card>
          <EmptyState
            icon="construct-outline"
            title="Not available yet"
            subtitle="On-device image generation needs a native rendering pipeline (Core ML on iOS, MNN/QNN on Android) that hasn't been built. Chat, Vision, and Voice are fully on-device already."
          />
        </Card>

        <TextInput
          editable={false}
          style={[styles.input, { borderColor: colors.border, backgroundColor: colors.surfaceAlt, color: colors.textMuted }]}
          placeholder="A dog wearing sunglasses..."
          placeholderTextColor={colors.textMuted}
        />
        <Button label="Generate" onPress={() => {}} disabled icon="color-wand-outline" />
        <Text style={[typography.caption, { color: colors.textMuted, textAlign: 'center' }]}>Coming in a future update.</Text>
      </View>
    </Screen>
  );
}

const styles = StyleSheet.create({
  input: { borderWidth: StyleSheet.hairlineWidth, borderRadius: radius.md, padding: spacing.md, fontSize: 15, minHeight: 60 },
});
