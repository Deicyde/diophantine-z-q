// Executed in a bounded child so an artifact service stall cannot stall compilation.
const fs = require('node:fs');
const path = require('node:path');
const {DefaultArtifactClient} = require('@actions/artifact');
(async () => {
  const [directory, name] = process.argv.slice(2);
  if (!/^kernel-progress-[0-9]+-[0-9]{3}$/.test(name)) throw new Error('Invalid artifact name');
  const files = fs.readdirSync(directory).map(n => path.join(directory, n));
  const result = await new DefaultArtifactClient().uploadArtifact(name, files, directory,
    {retentionDays: 14, compressionLevel: 1});
  if (!result.id) throw new Error('No confirmed artifact ID');
  console.log('[kernel resource artifact] '+JSON.stringify({name, ...result}));
})().catch(error => {console.error('Resource upload failed:', error.message); process.exitCode = 1;});
