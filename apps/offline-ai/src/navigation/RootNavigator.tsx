import { NavigationContainer } from '@react-navigation/native';
import { createBottomTabNavigator } from '@react-navigation/bottom-tabs';
import ChatScreen from '../screens/ChatScreen';
import ImageGenScreen from '../screens/ImageGenScreen';
import VoiceScreen from '../screens/VoiceScreen';
import VisionScreen from '../screens/VisionScreen';
import ModelBrowserScreen from '../screens/ModelBrowserScreen';
import SettingsScreen from '../screens/SettingsScreen';

export type RootTabParamList = {
  Chat: undefined;
  ImageGen: undefined;
  Voice: undefined;
  Vision: undefined;
  Models: undefined;
  Settings: undefined;
};

const Tab = createBottomTabNavigator<RootTabParamList>();

export default function RootNavigator() {
  return (
    <NavigationContainer>
      <Tab.Navigator initialRouteName="Chat">
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
