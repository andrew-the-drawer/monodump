import { useEffect, useState } from 'react';

/**
 * Generic subscriber-pattern binding: get the service's current state
 * immediately on mount, subscribe for updates, unsubscribe on unmount.
 * Keeps screens as pure views over service-owned state instead of
 * duplicating it into component state.
 */
export function useServiceSnapshot<T>(subscribe: (listener: (snapshot: T) => void) => () => void, getSnapshot: () => T): T {
  const [snapshot, setSnapshot] = useState<T>(getSnapshot);

  useEffect(() => {
    const unsubscribe = subscribe(setSnapshot);
    return unsubscribe;
  }, [subscribe]);

  return snapshot;
}
