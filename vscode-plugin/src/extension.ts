// The module 'vscode' contains the VS Code extensibility API
// Import the module and reference it with the alias vscode in your code below
import * as vscode from 'vscode';
import * as vscodelang from 'vscode-languageclient';

let client: vscodelang.LanguageClient;

// This method is called when the "duolang-client" extension is activated.
export function activate(context: vscode.ExtensionContext) {
	
	console.log('Congratulations, your extension "duolang-client" is now active!');
    
	let config = vscode.workspace.getConfiguration("duolang-client");

	let defaultCmd = "duo";
	let duolangCmd = config.get<string>("executable") || defaultCmd;

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
            command: duolangCmd,
            args: args,
            options: {}
        },
        debug: {
            command: duolangCmd,
            args: args,
            options: {}
        }
    };

    let clientOptions: vscodelang.LanguageClientOptions = {
        documentSelector: [{
            scheme: 'file',
            language: 'duolang'
        }],
        diagnosticCollectionName: "duolang"
    };

    client = new vscodelang.LanguageClient(
        'duolangLanguageServer',
        'Duo Language Server',
        serverOptions,
        clientOptions
    );

	context.subscriptions.push(client.start());
}

// this method is called when your extension is deactivated
export function deactivate() {}
