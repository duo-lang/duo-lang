// The module 'vscode' contains the VS Code extensibility API
// Import the module and reference it with the alias vscode in your code below
import * as vscode from 'vscode';
import * as vscodelang from 'vscode-languageclient';

let client: vscodelang.LanguageClient;

// This method is called when the "dualsub-client" extension is activated.
export function activate(context: vscode.ExtensionContext) {
	
	console.log('Congratulations, your extension "dualsub-client" is now active!');
    
	let config = vscode.workspace.getConfiguration("dualsub");

	let defaultCmd = "dualsub";
	let dualsubCmd = config.get<string>("executable") || defaultCmd;
	let args = ["lsp"];

	let serverOptions: vscodelang.ServerOptions = {
        run: {
            command: dualsubCmd,
            args: args,
            options: {}
        },
        debug: {
            command: dualsubCmd,
            args: args.concat(["--debug"]), // Not implemented in the LSP Server!
            options: {}
        }
    };

    let clientOptions: vscodelang.LanguageClientOptions = {
        documentSelector: [{
            scheme: 'file',
            language: 'dualsub'
        }],
        diagnosticCollectionName: "dualsub"
    };

    client = new vscodelang.LanguageClient(
        'dualsubLanguageServer',
        'DualSub Language Server',
        serverOptions,
        clientOptions
    );

	context.subscriptions.push(client.start());
}

// this method is called when your extension is deactivated
export function deactivate() {}
