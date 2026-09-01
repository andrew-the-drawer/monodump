import { useColorScheme } from 'react-native';

const light = {
  background: '#F7FAF9',
  surface: '#FFFFFF',
  surfaceAlt: '#EFF6F4',
  border: '#E1E9E7',
  textPrimary: '#0F172A',
  textSecondary: '#54655F',
  textMuted: '#93A29D',
  primary: '#0D9488',
  primarySoft: '#CCFBF1',
  onPrimary: '#FFFFFF',
  accent: '#F97316',
  accentSoft: '#FFEDD5',
  danger: '#DC2626',
  dangerSoft: '#FEE2E2',
  success: '#16A34A',
  vision: '#7C3AED',
  visionSoft: '#EDE9FE',
  overlay: 'rgba(15, 23, 42, 0.4)',
};

const dark = {
  background: '#0A0F0F',
  surface: '#141C1B',
  surfaceAlt: '#1B2524',
  border: '#263130',
  textPrimary: '#EAF6F4',
  textSecondary: '#9FB0AE',
  textMuted: '#657573',
  primary: '#2DD4BF',
  primarySoft: '#0F3B35',
  onPrimary: '#04201C',
  accent: '#FB923C',
  accentSoft: '#3A2313',
  danger: '#F87171',
  dangerSoft: '#3B1616',
  success: '#4ADE80',
  vision: '#A78BFA',
  visionSoft: '#2B2141',
  overlay: 'rgba(0, 0, 0, 0.55)',
};

export type ThemeColors = typeof light;

export const spacing = { xs: 4, sm: 8, md: 12, lg: 16, xl: 20, xxl: 24, xxxl: 32 } as const;
export const radius = { sm: 8, md: 12, lg: 16, xl: 20, full: 999 } as const;

export const typography = {
  title: { fontSize: 20, fontWeight: '700' as const },
  subtitle: { fontSize: 15, fontWeight: '600' as const },
  body: { fontSize: 15, fontWeight: '400' as const, lineHeight: 22 },
  caption: { fontSize: 12, fontWeight: '600' as const, letterSpacing: 0.3 },
  micro: { fontSize: 11, fontWeight: '600' as const, letterSpacing: 0.2 },
};

/** Subtle, consistent elevation — one step for cards, a stronger one for floating action controls. */
export const elevation = {
  card: {
    shadowColor: '#0F172A',
    shadowOpacity: 0.06,
    shadowRadius: 10,
    shadowOffset: { width: 0, height: 3 },
    elevation: 2,
  },
  floating: {
    shadowColor: '#0F172A',
    shadowOpacity: 0.18,
    shadowRadius: 16,
    shadowOffset: { width: 0, height: 6 },
    elevation: 6,
  },
};

export function useTheme() {
  const scheme = useColorScheme();
  const isDark = scheme === 'dark';
  return { colors: isDark ? dark : light, spacing, radius, typography, elevation, isDark };
}
