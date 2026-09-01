import { DarkTheme, DefaultTheme, NavigationContainer } from '@react-navigation/native';
import { createBottomTabNavigator } from '@react-navigation/bottom-tabs';
import { Ionicons } from '@expo/vector-icons';
import ChatScreen from '../screens/ChatScreen';
import ImageGenScreen from '../screens/ImageGenScreen';
import VoiceScreen from '../screens/VoiceScreen';
import VisionScreen from '../screens/VisionScreen';
import ModelBrowserScreen from '../screens/ModelBrowserScreen';
import SettingsScreen from '../screens/SettingsScreen';
import { useTheme } from '../theme/theme';

export type RootTabParamList = {
  Chat: undefined;
  ImageGen: undefined;
  Voice: undefined;
  Vision: undefined;
  Models: undefined;
  Settings: undefined;
};

const TAB_ICONS: Record<keyof RootTabParamList, keyof typeof Ionicons.glyphMap> = {
  Chat: 'chatbubbles',
  ImageGen: 'color-palette',
  Voice: 'mic',
  Vision: 'eye',
  Models: 'cube',
  Settings: 'settings',
};

const Tab = createBottomTabNavigator<RootTabParamList>();

export default function RootNavigator() {
  const { colors, isDark } = useTheme();

  const navigationTheme = {
    ...(isDark ? DarkTheme : DefaultTheme),
    colors: {
      ...(isDark ? DarkTheme.colors : DefaultTheme.colors),
      background: colors.background,
      card: colors.surface,
      border: colors.border,
      primary: colors.primary,
      text: colors.textPrimary,
    },
  };

  return (
    <NavigationContainer theme={navigationTheme}>
      <Tab.Navigator
        initialRouteName="Chat"
        screenOptions={({ route }) => ({
          headerShown: false,
          tabBarActiveTintColor: colors.primary,
          tabBarInactiveTintColor: colors.textMuted,
          tabBarStyle: { backgroundColor: colors.surface, borderTopColor: colors.border },
          tabBarIcon: ({ color, size, focused }) => (
            <Ionicons name={focused ? TAB_ICONS[route.name] : (`${TAB_ICONS[route.name]}-outline` as keyof typeof Ionicons.glyphMap)} color={color} size={size} />
          ),
        })}
      >
        <Tab.Screen name="Chat" component={ChatScreen} options={{ title: 'Chat' }} />
        <Tab.Screen name="ImageGen" component={ImageGenScreen} options={{ title: 'Image' }} />
        <Tab.Screen name="Voice" component={VoiceScreen} options={{ title: 'Voice' }} />
        <Tab.Screen name="Vision" component={VisionScreen} options={{ title: 'Vision' }} />
        <Tab.Screen name="Models" component={ModelBrowserScreen} options={{ title: 'Models' }} />
        <Tab.Screen name="Settings" component={SettingsScreen} options={{ title: 'Settings' }} />
      </Tab.Navigator>
    </NavigationContainer>
  );
}
