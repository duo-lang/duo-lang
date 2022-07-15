// The module 'vscode' contains the VS Code extensibility API
// Import the module and reference it with the alias vscode in your code below
import * as vscode from 'vscode';
import * as vscodelang from 'vscode-languageclient';

let client: vscodelang.LanguageClient;

// This method is called when the "duo-lang-client" extension is activated.
export function activate(context: vscode.ExtensionContext) {
	
	console.log('Congratulations, your extension "duo-lang-client" is now active!');
    
	let config = vscode.workspace.getConfiguration("duo-lang-client");

	let defaultCmd = "duo";
	let duoLangCmd = config.get<string>("executable") || defaultCmd;

    // Assemble arguments
    let args: string[] = [];
    args.push("lsp");

    let logconfig = config.get<string>("logfile");
    if (!(logconfig === undefined || logconfig.length === 0)) {
        args.push("--logfile");
        args.push(logconfig);
    }

	let serverOptions: vscodelang.ServerOptions = {
        run: {
            command: duoLangCmd,
            args: args,
            options: {}
        },
        debug: {
            command: duoLangCmd,
            args: args,
            options: {}
        }
    };

    let clientOptions: vscodelang.LanguageClientOptions = {
        documentSelector: [{
            scheme: 'file',
            language: 'duo-lang'
        }],
        diagnosticCollectionName: "duo-lang"
    };

    client = new vscodelang.LanguageClient(
        'duo-langLanguageServer',
        'Duo Language Server',
        serverOptions,
        clientOptions
    );

	context.subscriptions.push(client.start());
}

// this method is called when your extension is deactivated
export function deactivate() {}
