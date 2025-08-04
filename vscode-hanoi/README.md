# Hanoi Language Support for VS Code

This extension provides syntax highlighting, formatting, and language support for the Hanoi programming language.

## Features

- **Syntax Highlighting**: Full syntax highlighting for Hanoi language constructs
- **Code Formatting**: Automatic code formatting with configurable indentation
- **IntelliSense**: Auto-completion for keywords and builtin functions
- **Hover Information**: Documentation for builtin functions on hover
- **Bracket Matching**: Automatic bracket matching and auto-closing
- **Comment Support**: Line comments (`//`) and block comments (`/* */`)

## Language Features

The extension recognizes and highlights:

- **Keywords**: `fn`, `mod`, `use`, `sentence`, `let`, `if`, `else`, `match`, `nil`, `true`, `false`
- **Builtins**: `#add`, `#sub`, `#prod`, `#eq`, `#lt`, `#ord`, `#cons`, `#snoc`, `#tuple`, `#untuple`, `#nil`, `#some`, `#none`
- **Symbols**: `@symbol` and `@"string symbols"`
- **Strings**: Double-quoted strings with escape sequences
- **Characters**: Single-quoted characters
- **Numbers**: Integer literals
- **Comments**: Line and block comments

## Configuration

The extension provides the following configuration options:

- `hanoi.format.enable`: Enable/disable Hanoi formatting (default: true)
- `hanoi.format.indentSize`: Number of spaces for indentation (default: 4)

## Usage

1. Open a `.han` file in VS Code
2. The extension will automatically activate and provide syntax highlighting
3. Use `Ctrl+Shift+P` (or `Cmd+Shift+P` on Mac) and run "Format Document" to format your code
4. Hover over builtin functions (starting with `#`) to see documentation
5. Use auto-completion by typing keywords or builtin function names

## Example

```hanoi
use 'crate::builtin;

mod example {
    fn (a, b) add => {
        let result = (a, b) #add;
        result
    }

    sentence hello {
        #nil
    }
}
```

## Development

To build the extension:

1. Install dependencies: `npm install`
2. Compile TypeScript: `npm run compile`
3. Package the extension: `vsce package`

## Contributing

Contributions are welcome! Please feel free to submit issues and pull requests.

## License

MIT License - see LICENSE file for details. 