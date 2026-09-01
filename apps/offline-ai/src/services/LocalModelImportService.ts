import * as DocumentPicker from 'expo-document-picker';
import { Directory, File, Paths } from 'expo-file-system';
import { parseModelFilename } from '../utils/modelFilename';
import type { ModelInfo } from '../types/model';

const modelsDirectory = new Directory(Paths.document, 'models');

/**
 * Some users already have a .gguf on-device and don't want to re-download.
 * Android hands back a content:// URI, not a real path, so it has to be
 * copied into app storage before llama.rn can open it.
 */
class LocalModelImportService {
  async pickAndImport(): Promise<ModelInfo | null> {
    const result = await DocumentPicker.getDocumentAsync({
      type: ['application/octet-stream', '*/*'],
      copyToCacheDirectory: false,
    });
    if (result.canceled || !result.assets[0]) return null;

    const asset = result.assets[0];
    if (!asset.name.toLowerCase().endsWith('.gguf')) {
      throw new Error('Please pick a .gguf model file.');
    }

    if (!modelsDirectory.exists) {
      modelsDirectory.create({ idempotent: true });
    }

    const source = new File(asset.uri);
    await source.copy(modelsDirectory);
    const destination = new File(modelsDirectory, asset.name);

    const { name, quant } = parseModelFilename(asset.name);

    return {
      id: `local:${asset.name}`,
      displayName: name,
      organization: 'Imported',
      capability: 'text',
      quant: quant ?? 'q4_k_m',
      file: { filename: destination.uri, sizeBytes: destination.size },
    };
  }
}

export const localModelImportService = new LocalModelImportService();
