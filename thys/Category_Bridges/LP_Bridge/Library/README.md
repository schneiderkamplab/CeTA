# Native LP proof dependency cache

The parent session loads the existing native LP theories without modifying them.
This keeps repeated category-bridge builds from rebuilding their checker dependencies.
