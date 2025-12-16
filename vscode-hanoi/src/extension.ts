import * as vscode from 'vscode';
import { DebugAdapterServer, DebugAdapterDescriptorFactory, DebugAdapterExecutable, ProviderResult, DebugAdapterDescriptor } from 'vscode';

export function activate(context: vscode.ExtensionContext) {
    console.log('Hanoi Language Support is now active!');

    // Register formatter
    const formatter = vscode.languages.registerDocumentFormattingEditProvider('hanoi', {
        provideDocumentFormattingEdits(document: vscode.TextDocument): vscode.TextEdit[] {
            const edits: vscode.TextEdit[] = [];
            const text = document.getText();
            const lines = text.split('\n');
            const config = vscode.workspace.getConfiguration('hanoi.format');
            const indentSize = config.get<number>('indentSize', 4);
            const indentChar = ' '.repeat(indentSize);

            let currentIndent = 0;
            let inString = false;
            let inChar = false;
            let inComment = false;
            let bracketStack: string[] = [];

            for (let i = 0; i < lines.length; i++) {
                const line = lines[i];
                let formattedLine = line.trim();

                // Skip empty lines
                if (formattedLine === '') {
                    edits.push(vscode.TextEdit.replace(
                        new vscode.Range(i, 0, i, line.length),
                        ''
                    ));
                    continue;
                }

                // Handle comments
                if (formattedLine.startsWith('//')) {
                    edits.push(vscode.TextEdit.replace(
                        new vscode.Range(i, 0, i, line.length),
                        indentChar.repeat(currentIndent) + formattedLine
                    ));
                    continue;
                }

                // Count brackets for indentation
                let newIndent = currentIndent;
                for (let j = 0; j < formattedLine.length; j++) {
                    const char = formattedLine[j];
                    
                    // Handle strings and characters
                    if (char === '"' && !inChar) {
                        inString = !inString;
                    } else if (char === "'" && !inString) {
                        inChar = !inChar;
                    } else if (!inString && !inChar) {
                        // Handle brackets
                        if (char === '{' || char === '(' || char === '[') {
                            bracketStack.push(char);
                        } else if (char === '}' || char === ')' || char === ']') {
                            const openBracket = bracketStack.pop();
                            if (openBracket) {
                                // Decrease indent for closing brackets
                                if (j === 0) {
                                    newIndent = Math.max(0, newIndent - 1);
                                }
                            }
                        }
                    }
                }

                // Apply indentation
                const finalLine = indentChar.repeat(newIndent) + formattedLine;
                edits.push(vscode.TextEdit.replace(
                    new vscode.Range(i, 0, i, line.length),
                    finalLine
                ));

                // Update indent for next line
                currentIndent = newIndent;
                
                // Increase indent for opening brackets at end of line
                const lastChar = formattedLine[formattedLine.length - 1];
                if (lastChar === '{' || lastChar === '(' || lastChar === '[') {
                    currentIndent++;
                }
            }

            return edits;
        }
    });

    context.subscriptions.push(formatter);

    // Register hover provider for builtins
    const hoverProvider = vscode.languages.registerHoverProvider('hanoi', {
        provideHover(document, position, token) {
            const range = document.getWordRangeAtPosition(position);
            const word = document.getText(range);

            // Provide hover information for builtins
            if (word.startsWith('#')) {
                const builtinName = word.substring(1);
                const builtinDocs: { [key: string]: string } = {
                    'add': 'Builtin function: adds two numbers',
                    'sub': 'Builtin function: subtracts second number from first',
                    'prod': 'Builtin function: multiplies two numbers',
                    'eq': 'Builtin function: checks if two values are equal',
                    'lt': 'Builtin function: checks if first value is less than second',
                    'ord': 'Builtin function: gets character code',
                    'cons': 'Builtin function: prepends element to list',
                    'snoc': 'Builtin function: appends element to list',
                    'tuple': 'Builtin function: creates tuple',
                    'untuple': 'Builtin function: destructures tuple',
                    'nil': 'Builtin value: empty list',
                    'some': 'Builtin value: wraps a value',
                    'none': 'Builtin value: represents absence of value'
                };

                const doc = builtinDocs[builtinName];
                if (doc) {
                    return new vscode.Hover([
                        `**${word}**`,
                        doc
                    ]);
                }
            }

            return null;
        }
    });

    context.subscriptions.push(hoverProvider);

    // Register completion provider
    const completionProvider = vscode.languages.registerCompletionItemProvider('hanoi', {
        provideCompletionItems(document, position, token, context) {
            const completions: vscode.CompletionItem[] = [];

            // Keywords
            const keywords = [
                'fn', 'mod', 'use', 'sentence', 'let', 'if', 'else', 'match',
                'nil', 'true', 'false', 'and_then', 'then', 'await', 'do', 'loop'
            ];

            keywords.forEach(keyword => {
                const item = new vscode.CompletionItem(keyword, vscode.CompletionItemKind.Keyword);
                item.detail = 'Hanoi keyword';
                completions.push(item);
            });

            // Builtins
            const builtins = [
                'add', 'sub', 'prod', 'eq', 'lt', 'ord', 'cons', 'snoc',
                'tuple', 'untuple', 'nil', 'some', 'none'
            ];

            builtins.forEach(builtin => {
                const item = new vscode.CompletionItem(`#${builtin}`, vscode.CompletionItemKind.Function);
                item.detail = 'Hanoi builtin';
                completions.push(item);
            });

            // Qualified labels
            const qualifiedLabels = [
                'crate::builtin', 'super::split_iter', 'cases::parse_empty',
                'cases::parse_some', 'super::super::parseint'
            ];

            qualifiedLabels.forEach(label => {
                const item = new vscode.CompletionItem(`'${label}`, vscode.CompletionItemKind.Function);
                item.detail = 'Hanoi qualified label';
                completions.push(item);
            });

            return completions;
        }
    }, '#', '@', 'f', 'm', 'u', 's', 'l', 'i', 'e', 'n', 't', 'a', 'd');

    context.subscriptions.push(completionProvider);

    // Register debug adapter factory
    const debugAdapterFactory = new HanoiDebugAdapterFactory();
    context.subscriptions.push(
        vscode.debug.registerDebugAdapterDescriptorFactory('hanoi', debugAdapterFactory)
    );
}

class HanoiDebugAdapterFactory implements DebugAdapterDescriptorFactory {
    createDebugAdapterDescriptor(
        session: vscode.DebugSession,
        executable: DebugAdapterExecutable | undefined
    ): ProviderResult<DebugAdapterDescriptor> {
        const config = session.configuration;
        const port = config.port || vscode.workspace.getConfiguration('hanoi').get<number>('debuggerPort', 4711);
        const host = config.host || 'localhost';

        // Connect to DAP server via TCP/IP
        return new DebugAdapterServer(port, host);
    }
}

export function deactivate() {} 