const { getDefaultConfig } = require('expo/metro-config');
const path = require('path');

const projectRoot = __dirname;
const workspaceRoot = path.resolve(projectRoot, '../..');

const config = getDefaultConfig(projectRoot);

// Needed once the app depends on a workspace package (@monodump/react-native-image-gen) —
// pnpm keeps each package's deps under its own node_modules via symlinks rather than a
// single flat hoisted tree, so Metro has to be told explicitly where else to look.
config.watchFolders = [workspaceRoot];
config.resolver.nodeModulesPaths = [path.resolve(projectRoot, 'node_modules'), path.resolve(workspaceRoot, 'node_modules')];
config.resolver.disableHierarchicalLookup = true;

module.exports = config;
