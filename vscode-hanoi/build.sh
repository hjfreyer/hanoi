#!/bin/bash

# Build script for Hanoi VSCode extension

echo "Building Hanoi VSCode extension..."

# Install dependencies if node_modules doesn't exist
if [ ! -d "node_modules" ]; then
    echo "Installing dependencies..."
    npm install
fi

# Compile TypeScript
echo "Compiling TypeScript..."
npm run compile

# Check if compilation was successful
if [ $? -eq 0 ]; then
    echo "Compilation successful!"
    
    # Package the extension
    echo "Packaging extension..."
    npx vsce package
    
    if [ $? -eq 0 ]; then
        echo "Extension packaged successfully!"
        echo "You can now install the .vsix file in VSCode"
    else
        echo "Failed to package extension"
        exit 1
    fi
else
    echo "Compilation failed!"
    exit 1
fi 