# Development Guide

This guide explains how to develop and test the Hanoi VSCode extension.

## Prerequisites

- Node.js (version 16 or higher)
- npm or yarn
- VSCode
- VSCode Extension Development Host

## Setup

1. Clone the repository
2. Navigate to the extension directory: `cd vscode-hanoi`
3. Install dependencies: `npm install`
4. Install VSCode Extension Manager: `npm install -g vsce`

## Development Workflow

### Building the Extension

**On Windows:**
```cmd
build.bat
```

**On Linux/macOS:**
```bash
chmod +x build.sh
./build.sh
```

**Manual build:**
```bash
npm run compile
npx vsce package
```

### Testing the Extension

1. Build the extension using one of the methods above
2. Open VSCode
3. Go to Extensions (Ctrl+Shift+X)
4. Click the "..." menu and select "Install from VSIX..."
5. Select the generated `.vsix` file
6. Open a `.han` file to test the extension

### Development Mode

For active development, you can run the extension in development mode:

1. Open the `vscode-hanoi` folder in VSCode
2. Press F5 to start the Extension Development Host
3. In the new VSCode window, open a `.han` file
4. Make changes to the extension code
5. Press Ctrl+R (or Cmd+R on Mac) to reload the extension

## File Structure

```
vscode-hanoi/
├── src/
│   └── extension.ts          # Main extension code
├── syntaxes/
│   └── hanoi.tmLanguage.json # TextMate grammar for syntax highlighting
├── samples/
│   └── example.han           # Sample Hanoi file for testing
├── package.json              # Extension manifest
├── language-configuration.json # Language configuration
├── tsconfig.json            # TypeScript configuration
└── README.md                # Extension documentation
```

## Key Components

### Syntax Highlighting

The syntax highlighting is defined in `syntaxes/hanoi.tmLanguage.json` using TextMate grammar. This file defines:

- Language patterns and rules
- Token scopes for different language constructs
- Regular expressions for matching syntax elements

### Language Configuration

`language-configuration.json` defines:

- Comment styles (line and block comments)
- Bracket matching and auto-closing
- Indentation rules
- Code folding markers

### Extension Features

The main extension (`src/extension.ts`) provides:

- **Formatter**: Automatic code formatting with configurable indentation
- **Hover Provider**: Documentation for builtin functions
- **Completion Provider**: Auto-completion for keywords and builtins

## Adding New Features

### Adding New Keywords

1. Update the grammar in `syntaxes/hanoi.tmLanguage.json`
2. Add the keyword to the completion provider in `src/extension.ts`
3. Update the hover provider if the keyword needs documentation

### Adding New Builtins

1. Add the builtin to the completion provider
2. Add documentation to the hover provider
3. Update the grammar if needed

### Modifying Formatting

The formatter logic is in the `provideDocumentFormattingEdits` function in `src/extension.ts`. It handles:

- Indentation based on brackets and blocks
- Comment formatting
- String and character literal preservation

## Testing

### Manual Testing

1. Create test files with various Hanoi constructs
2. Test syntax highlighting
3. Test formatting (Ctrl+Shift+P → "Format Document")
4. Test auto-completion
5. Test hover information

### Sample Test Cases

- Basic syntax: keywords, operators, literals
- Complex constructs: functions, modules, sentences
- Edge cases: nested brackets, comments in strings
- Formatting: various indentation scenarios

## Publishing

To publish the extension to the VSCode Marketplace:

1. Update the version in `package.json`
2. Build the extension: `npx vsce package`
3. Publish: `npx vsce publish`

## Troubleshooting

### Common Issues

1. **Extension not activating**: Check the `activationEvents` in `package.json`
2. **Syntax highlighting not working**: Verify the grammar file path and scope name
3. **Formatting not working**: Check the formatter registration in the extension
4. **Build errors**: Ensure all dependencies are installed and TypeScript is configured correctly

### Debug Tips

- Use the VSCode Developer Tools (Help → Toggle Developer Tools)
- Check the Output panel for extension logs
- Use the Problems panel for TypeScript errors
- Test with the sample files in the `samples/` directory 